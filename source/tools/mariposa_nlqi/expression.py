import numpy as np
from tabulate import tabulate
from configs import *
from copy import deepcopy

OP_PROB = {
    "add_": 0.1,
    "sub_": 0.1,
    "mul_": 0.8,
}

MOD_PROB = 0.1

OP_PRETTY = {
    "add_": "+",
    "sub_": "-",
    "mul_": "*",
    "mod_": "%",
}

class Operator(enum.Enum):
    ADD = "add_"
    SUB = "sub_"
    MUL = "mul_"
    MOD = "mod_"

    @classmethod
    def random_init(cls):
        r = random.random()
        if r <= OP_PROB[Operator.ADD.value]:
            return Operator.ADD
        if r <= OP_PROB[Operator.ADD.value] + OP_PROB[Operator.SUB.value]:
            return Operator.SUB
        return Operator.MUL

class Expression:
    def __init__(self, op, left, right, suffix=""):
        self.op = op
        self.suffix = suffix

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
    def var_init(cls, var, suffix=""):
        v = cls(None, None, None, suffix)
        v.value = var + str(suffix)
        return v

    @classmethod
    def random_init(cls, suffix, max_depth, prob=1):
        op = Operator.random_init()
        if max_depth == 0 or random.random() > prob:
            left, right, op = None, None, None
        else:
            left = Expression.random_init(suffix, max_depth-1, prob*EARLY_STOP_FACTOR)
            right = Expression.random_init(suffix, max_depth-1, prob*EARLY_STOP_FACTOR)
        e = cls(op, left, right, suffix)
        if random.random() <= MOD_PROB:
            m = Expression.var_init("m" + str(suffix))
            return cls(Operator.MOD, e, m, suffix)
        else:
            return e

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
            if "as int)" not in self.value:
                return {self.value}
            else:
                return set()
        return self.left.get_vars() | self.right.get_vars()

    def get_unique_subexps(self):
        if self.op == None:
            return {str(self)}
        return {str(self)} | self.left.get_unique_subexps() | self.right.get_unique_subexps()

    # self is the skeleton, other is the expression
    def get_substitution(self, other):
        if self.op == None:
            return {self.value: other}

        if self.op != other.op:
            return None

        left_subs = self.left.get_substitution(other.left)
        right_subs = self.right.get_substitution(other.right)
        if left_subs == None or right_subs == None:
            return None
        return {**left_subs, **right_subs}

    # self is the skeleton
    def apply_substitution(self, subs, suffix, expand=False):
        if self.op == None:
            if self.value in subs:
                return deepcopy(subs[self.value])
            if expand:
                ne = Expression.random_init(suffix, 2)
                subs[self.value] = ne
                return ne
            assert False
        return Expression(deepcopy(self.op), 
                    self.left.apply_substitution(subs, suffix, expand), 
                    self.right.apply_substitution(subs, suffix, expand))

    def replace(self, new):
        self.op = new.op
        self.suffix = new.suffix
        self.value = new.value
        self.left = new.left
        self.right = new.right
        
    def list_op_nodes(self):
        if self.op == None:
            return []
        else:
            return [self] + self.left.list_op_nodes() + self.right.list_op_nodes()

    def __str__(self):
        if self.op == None:
            return str(self.value)
        return "(%s(%s, %s))" % (self.op.value, self.left,self.right)

    def to_str(self, pretty=False):
        if self.op == None:
            return str(self.value)
        if not pretty:
            return str(self)
        if self.op == Operator.MOD:
            return "(%s %% %s)" % (self.left.to_str(pretty), self.right.to_str(pretty))
        op = OP_PRETTY[self.op.value]
        return "(%s %s %s)" % (self.left.to_str(pretty), op, self.right.to_str(pretty))

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
