import random
import enum
import numpy as np
from tabulate import tabulate

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

class StepMode(enum.Enum):
    INST_HINT = "inst_hint"
    INST_ONLY = "inst_only"
    AUTO_HINT = "auto_hint"
    AUTO_ONLY = "auto_only"
    NL_HINT = "nl_arith_hint"
    NL_ONLY = "nl_arith_only"
    STEPPED_INST_AUTO = "stepped_inst_auto"

class LemmaCall:
    def __init__(self, name, args):
        self.name = name
        self.args = args
        
        self.inst_call = "lemma_%s(%s);" % (self.name, ", ".join([str(a) for a in self.args]))
        self.auto_call = "lemma_mul_properties_auto(); "
        self.hint_call = None

    def set_hint(self, left, right):
        # print(left, right)
        self.hint_call = "assert (%s == %s)" % (left, right)

    def emit(self, mode):
        if mode == StepMode.AUTO_ONLY: 
            return self.auto_call

        if mode == StepMode.NL_ONLY:
            return ""

        if mode == StepMode.INST_ONLY:
            return self.inst_call

        if mode == StepMode.INST_HINT:
            return self.inst_call + " " + self.hint_call

        assert self.hint_call != None

        if mode == StepMode.AUTO_HINT:
            return self.hint_call + " by {" + self.auto_call + "}"

        if mode == StepMode.NL_HINT:
            return self.hint_call

        assert False

def pick_side(left, right):
    if left and right:
        if random.random() < 0.5:
            left = False
        else:
            right = False
    assert left + right <= 1
    return left, right

class Expression:
    def __init__(self, op, left, right):
        self.op = op

        if op == None:
            assert left == None and right == None
            if random.random() <= TERM_VAR_PROB:
                self.value = random.choice(VARS)
            else:
                self.value = f"({int(random.random()*100)} as int)"
            return

        self.value = None
        self.left = left
        self.right = right

    @classmethod
    def random_init(cls, max_depth, prob=1):
        op = Operator.new()
        if max_depth == 0 or random.random() > prob:
            left, right, op = None, None, None
        else:
            left = Expression.random_init(max_depth-1, prob*EARLY_STOP_PROB_MULTIPLIER)
            right = Expression.random_init(max_depth-1, prob*EARLY_STOP_PROB_MULTIPLIER)
        return cls(op, left, right)

    def get_layer_stats(self, depth=0):
        if self.op == None:
            return {depth: 1}
        else:
            left_stats = self.left.get_layer_stats(depth+1)
            right_stats = self.right.get_layer_stats(depth+1)
            for k in right_stats:
                if k in left_stats:
                    left_stats[k] += right_stats[k]
                else:
                    left_stats[k] = right_stats[k]

            left_stats[depth] = 1
            return left_stats

    # def get_total_subexpression_count(self):
    #     if self.op == None:
    #         return 1
    #     return 1 + self.left.get_total_subexpression_count() + self.right.get_total_subexpression_count()

    def get_unique_subexps(self):
        if self.op == None:
            return {str(self)}
        return {str(self)} | self.left.get_unique_subexps() | self.right.get_unique_subexps()

    def list_op_nodes(self):
        if self.op == None:
            return []
        else:
            return [self] + self.left.list_op_nodes() + self.right.list_op_nodes()

    def associative_rewrite(self):
        call = None

        if self.op != Operator.MUL:
            return call

        left_enable, right_enable = pick_side(self.left.op == self.op, 
                                            self.right.op == self.op)

        orig = str(self)

        if left_enable:
            call = LemmaCall("mul_is_associative", [self.left.left, self.left.right, self.right])
            t_left = self.left
            self.left = t_left.left
            self.right = Expression(self.op, t_left.right, self.right)
            call.set_hint(orig, str(self))

        if right_enable:
            call = LemmaCall("mul_is_associative", [self.left, self.right.left, self.right.right])
            t_right = self.right
            self.right = t_right.right
            self.left = Expression(self.op, self.left, t_right.left)
            call.set_hint(orig, str(self))

        return call
    
    def commutative_rewrite(self):
        if self.op != Operator.MUL:
            return None
        orig = str(self)
        call = LemmaCall("mul_is_commutative", [self.left, self.right])
        t_right, t_left = self.right, self.left
        self.left, self.right = t_right, t_left
        call.set_hint(orig, str(self))
        return call

    def mul_distributive_rewrite(self):
        call = None

        if self.op != Operator.MUL:
            return call

        left_enable, right_enable = pick_side(self.left.op in {Operator.ADD, Operator.SUB},
                                            self.right.op in {Operator.ADD, Operator.SUB})

        orig = str(self)

        t_right, t_left = self.right, self.left

        if left_enable:
            call =  LemmaCall("mul_is_distributive", [self.left.left, self.left.right, self.right])
            op = self.left.op
            self.left = Expression(Operator.MUL, t_left.left, t_right)
            self.right = Expression(Operator.MUL, t_left.right, t_right)
            self.op = op
            call.set_hint(orig, str(self))

        if right_enable:
            call =  LemmaCall("mul_is_distributive", [self.left, self.right.left, self.right.right])
            op = self.right.op
            self.left = Expression(Operator.MUL, t_left, t_right.left)
            self.right = Expression(Operator.MUL, t_left, t_right.right)
            self.op = op
            call.set_hint(orig, str(self))

        return call

    def mul_add_distributive_inverse_rewrite(self):
        call = None
    
        if self.left.op != Operator.MUL or \
            self.right.op != Operator.MUL:
            return call
        
        if self.op not in {Operator.ADD, Operator.SUB}:
            return call

        left_enable, right_enable = pick_side(str(self.left.left) == str(self.right.left),
                                            str(self.left.right) == str(self.right.right))

        t_right, t_left = self.right, self.left

        orig = str(self)
        op = self.op

        if left_enable:
            x, y, z = t_left.left, t_left.right, t_right.right
            call =  LemmaCall("mul_is_distributive", [x, y, z])
            self.left = x
            self.right = Expression(op, y, z)
            self.op = Operator.MUL
            call.set_hint(orig, str(self))

        if right_enable:
            x, y, z = t_left.left, t_right.left, t_right.right
            call =  LemmaCall("mul_is_distributive", [x, y, z])
            self.left = Expression(op, x, y)
            self.right = z
            self.op = Operator.MUL
            call.set_hint(orig, str(self))

        return call

    def __str__(self):
        if self.op == None:
            return str(self.value)
        return "(%s%s%s)" % (self.left, self.op.value, self.right)

TERM_VAR_PROB = 0.95
TERM_CONST_PROB = 1 - TERM_VAR_PROB

EARLY_STOP_PROB_MULTIPLIER = 0.95

OP_PROB = {
    Operator.ADD: 0.1,
    Operator.SUB: 0.1,
    Operator.MUL: 0.8,
}

VARS = ["a", "b", "c", "d", "e"]

if __name__ == "__main__":
    table = [["depth", "mean\nunique\nsubexps", "mean\nunique\nsubexps\nper depth"]]
    for d in range(4, 20):
        values = []
        for i in range(20):
            e = Expression.random_init(d)
            # layers = e.get_layer_stats()
            # for i in sorted(layers):
            #     print(i, layers[i], round(layers[i] * 100 / 2 ** i, 2))
            values += [len(e.get_unique_subexps())]
        # print([d, int(np.mean(values)), round(np.mean(values)/ d, 2)])
        table.append([d, int(np.mean(values)), round(np.mean(values)/ d, 2)])
    print(tabulate(table, headers="firstrow"))
