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

        if mode == StepMode.INST_ONLY:
            for s in self.hidden:
                calls.append(s.call.emit(mode))
        return "\t\t\t{" + ";\n\t\t\t".join(calls) + ";}"

class Rewriter:
    def __init__(self, name, params):
        self.steps = []
        self.name = name

        retry_count = 0
        retry = True

        while retry:
            self.e = Expression.random_init(params.EXP_MAX_DEPTH)
            self.init_subexps = self.e.get_unique_subexps()
            self.start = str(self.e)

            for _ in range(params.TOTAL_STEPS):
                nodes = self.e.list_op_nodes()
                random.shuffle(nodes)

                fun = random.choice(FUNS)

                for n in nodes:
                    call = fun(n)
                    if call != None:
                        s = RewriteStep(len(self.steps)+1, call, str(self.e))
                        self.steps.append(s)
                        break

            if len(self.steps) < params.TOTAL_STEPS:
                retry = True
                self.steps = []
                retry_count += 1
            else:
                retry = False

            if retry_count > 10:
                print("[ERROR] exceeded retry count, decrease max_rewrites or increase max_depth?")
                exit(1)

        self.vars = self.e.get_vars()

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

    def mk_temp(self, i):
        return f"temp_{self.name}_{i}"

    def emit_temp_variables(self, csteps):
        lines = [f"\tlet {self.mk_temp(0)} = {self.start};"]
        for s in csteps:
            lines.append(f"\tlet {self.mk_temp(s.main.id)} = {s.main.result};")
        return lines

    def emit_as_calc(self, mode, upto, keep_every):
        csteps = self.get_steps(upto, keep_every)
        lines = self.emit_temp_variables(csteps)
        lines.append("\tcalc !{\n\t\t(==)")
        lines.append("\t\t" + self.mk_temp(0) + ";")
        for s in csteps:
            lines.append("\t\t" + s.emit_calls(mode) + "// " + str(s.main.id))
            lines.append("\t\t" + self.mk_temp(s.main.id) + ";")
        lines.append("\t}")
        return "\n".join(lines) + "\n"

    def emit_as_assert(self, mode, upto, keep_every):
        csteps = self.get_steps(upto, keep_every)
        lines = self.emit_temp_variables(csteps)
        prev = self.mk_temp(0)
        for s in csteps:
            lines.append("\tassert(" + prev + " == " + self.mk_temp(s.main.id) + ") by ")
            prev = self.mk_temp(s.main.id)
            lines.append(s.emit_calls(mode) + "// " + str(s.main.id))
        # lines.append("\tassert(" + prev + " == " + self.mk_temp(0) + ");")
        return "\n".join(lines) + "\n"

    def emit_as_lemma(self):
        args = ", ".join([v + ": int" for v in self.vars])
        lemma = f"""#[verifier::external_body]
pub proof fn lemma_test_{self.name}()
    ensures forall |{args}|
        #[trigger]({self.start})
        ==
        #[trigger]({self.steps[len(self.steps) - 1].result})
"""
        return lemma + "{}\n"

    # def emit_asserts_mixed(self, split):
    #     assert 0 <= split < len(self.steps)

    #     lines = [f"\t\tlet temp_0 = {self.start};"]

    #     for i, s in enumerate(self.steps[:split+1]):
    #         lines.append(f"\t\tlet temp_{i+1} = {s[1]};")

    #     for i, s in enumerate(self.steps[:split]):
    #         lines.append(f"\t\tassert(temp_{i} == temp_{i+1}) by ")
    #         lines.append("\t\t\t{" + s[0].emit(StepMode.INST_ONLY) + "}\t// " + str(i))

    #     i = split
    #     lines.append(f"\t\tassert(temp_{i} == temp_{i+1}) by ")
    #     lines.append("\t\t\t{" + s[0].emit(StepMode.AUTO_ONLY) + "}\t// " + str(i))

    #     return "\n".join(lines)

def get_func_sig(mode):
    args = ", ".join([v + ": int" for v in VARS])
    sig = f"pub proof fn lemma_test({args})"

    if mode == StepMode.NL_HINT or mode == StepMode.NL_ONLY:
        sig += " by (nonlinear_arith)"

    return [sig]

VERUS_HEADER = """use builtin_macros::*;
use builtin::*;
use crate::nl_basics::*;
verus! {

"""

VERUS_FOOTER ="""} // verus!"""

class Params:
    def __init__(self, seed):
        self.TOTAL_STEPS = 1
        self.EXP_MAX_DEPTH = 10
        self.EXP_NUM = 40

        random.seed(seed)
        self.seed = seed

        self.KEEP_EVERY = 1

    def __str__(self):
        return f"""[INFO] total number of rewrite steps: {self.TOTAL_STEPS}
[INFO] max depth of expressions: {self.EXP_MAX_DEPTH}
[INFO] number of expressions: {self.EXP_NUM}
[INFO] keep every: {self.KEEP_EVERY}
[INFO] seed: {self.seed}
"""

FUNS = [lambda e: e.commutative_rewrite(), 
        lambda e: e.associative_rewrite(), 
        lambda e: e.mul_distributive_rewrite(),
        lambda e: e.mul_add_distributive_inverse_rewrite()]

if __name__ == "__main__":
    if len(sys.argv) == 2:
        ts = int(sys.argv[1])
    else:
        ts = int.from_bytes(os.urandom(8), byteorder="big")

    pa0 = Params(ts)
    pa = Params(ts)
    print(pa, end="")

    pa0.EXP_MAX_DEPTH = 3
    pa0.TOTAL_STEPS = 1
    pa0.KEEP_EVERY = 1

    rws = []
    for i in range(pa.EXP_NUM):
        rws.append(Rewriter(i, pa))

    mode = StepMode.AUTO_ONLY
    for mode in [StepMode.AUTO_ONLY, StepMode.INST_ONLY]:
        mod_name = f"calc_{mode.value}"
        out_f = open(f"nl_qi_test/src/{mod_name}.rs", "w")
        out_f.write(VERUS_HEADER)

        # if mode == StepMode.AUTO_ONLY:
        # out_f.write("use vstd::calc_macro::*;\n");
        out_f.writelines(get_func_sig(mode) + ["\n{\n"])

        for rw in rws:
            out_f.write(rw.emit_as_assert(mode, pa.TOTAL_STEPS, pa.KEEP_EVERY))

        out_f.write("\n}\n")
        out_f.write(VERUS_FOOTER)
        out_f.close()