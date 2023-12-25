from expression import *
from axioms import *

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

class ExpRewriter(Expression):
    def __init__(self, op, left, right, suffix=""):
        super().__init__(op, left, right, suffix)

    @classmethod
    def random_init(cls, suffix, max_depth, prob=1):
        return super().random_init(suffix, max_depth, prob)

    def try_apply(self, nodes, ax, uf):
        random.shuffle(nodes)
        for n in nodes:
            res = ax.try_apply_lemma(n, uf)
            if res != None:
                return res
        return None

    def rewrite_single_step(self, uf):
        success = None
        nodes = list(self.list_op_nodes())

        # if random.randint(0, 1) < 0.5:
        #     success = self.try_apply(nodes, MOD_MUL_VANISH, uf)

        axioms = [ax for ax in AXIOMS]
        random.shuffle(axioms)
        while len(axioms) > 0 and not success:
            ax = axioms.pop()
            success = self.try_apply(nodes, ax, uf)
        
        if "% m)" in self.to_str(True):
            assert False

        assert success
        return success

class Rewriter:
    def __init__(self, eid, params):
        self.steps = []
        self.eid = eid
        self.ok = True

        if params.related:
            eid = ""
        self.e = ExpRewriter.random_init(eid, params.expr_max_depth)
        # self.init_subexps = self.e.get_unique_subexps()
        self.start = self.e.to_str(params.uf)

        for _ in range(params.steps_total):
            call = self.e.rewrite_single_step(params.uf)
            if call != None:
                s = RewriteStep(len(self.steps)+1, call, self.e.to_str(params.uf))
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

if __name__ == "__main__":
    # random.seed(0)
    e = ExpRewriter.random_init("", 3)
    print(e.to_str(True))
    for i in range(10):
        e.rewrite_single_step()
    print(e.to_str(True))
    # MUL_COMM.is_applicable(e)
