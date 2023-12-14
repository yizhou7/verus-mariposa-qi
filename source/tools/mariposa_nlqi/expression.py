import numpy as np
from tabulate import tabulate
from configs import *

class Operator(enum.Enum):
    ADD = "+"
    SUB = "-"
    MUL = "*"

    @classmethod
    def random_init(cls):
        r = random.random()
        if r <= OP_PROB[Operator.ADD.value]:
            return Operator.ADD
        if r <= OP_PROB[Operator.ADD.value] + OP_PROB[Operator.SUB.value]:
            return Operator.SUB
        return Operator.MUL

class LemmaCall:
    def __init__(self, name, args):
        self.name = name
        self.args = args

        self.inst_call = "lemma_%s(%s)" % (self.name, ", ".join([str(a) for a in self.args]))
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
            return self.inst_call

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
    def __init__(self, op, left, right, suffix=""):
        self.op = op

        if op == None:
            assert left == None and right == None
            if random.random() <= TERM_VAR_PROB:
                self.value = random.choice(VARS) + str(suffix)
            else:
                self.value = f"({int(random.random()*100)} as int)"
            return

        self.value = None
        self.left = left
        self.right = right

    @classmethod
    def random_init(cls, suffix, max_depth, prob=1):
        op = Operator.random_init()
        if max_depth == 0 or random.random() > prob:
            left, right, op = None, None, None
        else:
            left = Expression.random_init(suffix, max_depth-1, prob*EARLY_STOP_FACTOR)
            right = Expression.random_init(suffix, max_depth-1, prob*EARLY_STOP_FACTOR)
        return cls(op, left, right, suffix)

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
        
    def get_vars(self):
        if self.op == None:
            if self.value in VARS:
                return {self.value}
            else:
                return set()
        return self.left.get_vars() | self.right.get_vars()

    def get_unique_subexps(self):
        if self.op == None:
            return {str(self)}
        return {str(self)} | self.left.get_unique_subexps() | self.right.get_unique_subexps()

    def rewrite_associative(self):
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
    
    def rewrite_commutative(self):
        if self.op != Operator.MUL:
            return None
        orig = str(self)
        call = LemmaCall("mul_is_commutative", [self.left, self.right])
        t_right, t_left = self.right, self.left
        self.left, self.right = t_right, t_left
        call.set_hint(orig, str(self))
        return call

    def rewrite_mul_distributive(self):
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

    def rewrite_mul_add_distributive_inverse(self):
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

    def list_op_nodes(self):
        if self.op == None:
            return []
        else:
            return [self] + self.left.list_op_nodes() + self.right.list_op_nodes()

    def rewrite_single_step(self):
        retry_count = 0

        while retry_count < 10:
            nodes = self.list_op_nodes()
            random.shuffle(nodes)
            for n in nodes:
                fun = random.choice(FUNS)
                call = fun(n)
                if call != None:
                    return call
            retry_count += 1
        return None

    def __str__(self):
        if self.op == None:
            return str(self.value)
        return "(%s%s%s)" % (self.left, self.op.value, self.right)

FUNS = [lambda e: e.rewrite_commutative(), 
        lambda e: e.rewrite_associative(), 
        lambda e: e.rewrite_mul_distributive(),
        lambda e: e.rewrite_mul_add_distributive_inverse()]

if __name__ == "__main__":
    table = [["depth", "mean\nunique\nsubexps", "mean\nunique\nsubexps\nper depth"]]
    for d in range(5, 15):
        values = []
        for i in range(20):
            e = Expression.random_init("0", d)
            # layers = e.get_layer_stats()
            # for i in sorted(layers):
            #     print(i, layers[i], round(layers[i] * 100 / 2 ** i, 2))
            values += [len(e.get_unique_subexps())]
        # print([d, int(np.mean(values)), round(np.mean(values)/ d, 2)])
        table.append([d, int(np.mean(values)), round(np.mean(values)/ d, 2)])
    print(tabulate(table, headers="firstrow"))
