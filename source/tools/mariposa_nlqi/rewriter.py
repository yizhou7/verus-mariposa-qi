from expression import *
import sys, os

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

class Rewriter:
    def __init__(self, eid, params):
        self.steps = []
        self.eid = eid
        self.ok = True

        if params.related:
            eid = ""
        self.e = Expression.random_init(eid, params.expr_max_depth)
        # self.init_subexps = self.e.get_unique_subexps()
        self.start = str(self.e)

        for _ in range(params.steps_total):
            call = self.e.rewrite_single_step()
            if call != None:
                s = RewriteStep(len(self.steps)+1, call, str(self.e))
                self.steps.append(s)
            else:
                print("[ERROR] exceeded retry count, decrease steps_total or increase expr_max_depth?")
                self.ok = False
                return

        self.params = params
        self.vars = self.e.get_vars()
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
