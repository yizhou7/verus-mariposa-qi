import sys, os
from expression import *

class ExpandStep:
    def __init__(self, id, call, result):
        self.id = id
        self.call = call
        self.result = result

class RewriteStep:
    def __init__(self, id, call, result):
        self.id = id
        self.call = call
        self.result = result

class CompStep:
    def __init__(self, main, hidden):
        self.main = main
        self.hidden = hidden

    def emit_calls(self, mode):
        # if mode == StepMode.AUTO_ONLY:
        # return self.main.call
        calls = [self.main.call.emit(mode)]

        if mode == StepMode.INST:
            for s in self.hidden:
                calls.append(s.call.emit(mode))
        return "\t\t\t{" + ";\n\t\t\t".join(calls) + ";}"

class Expander:
    def __init__(self, eid, params):
        self.steps = []
        self.eid = eid
        self.ok = True

        if params.related:
            eid = ""

        self.e = Expression.random_init(eid, params.expr_max_depth)
        pe = self.e
        self.start = str(self.e)

        for i in range(params.steps_total):
            if i % 2 == 0:
                ce = Expression.random_init(eid, params.expr_max_depth)
                ne = Expression(Operator.MUL, pe, ce)
                call = LemmaCall("mul_monotonic", [pe, ce])
                pe = ne
                s = ExpandStep(len(self.steps)+1, call, ne)
            else:
                call = pe.rewrite_single_step()
                s = RewriteStep(len(self.steps)+1, call, str(pe))
                self.steps.append(s)

            # print(call.emit(StepMode.AUTO))
            self.steps.append(s)
        self.csteps = self.get_steps(params.steps_total, params.keep_every)

    def get_steps(self, upto, keep_every):
        steps = self.steps[:upto]
        assert 0 <= keep_every <= upto
        compressed = []

        between = []
        for s in steps:
            if s.id % keep_every == 0:
                compressed.append(CompStep(s, between))
                between = []
            else:
                between += [s]
        return compressed

if __name__ == "__main__":
    if len(sys.argv) == 3:
        ts = int(sys.argv[2])
    else:
        ts = int.from_bytes(os.urandom(8), byteorder="big")

    pa = EmitterParams(ts, config_name=sys.argv[1])
    Expander(0, pa)
