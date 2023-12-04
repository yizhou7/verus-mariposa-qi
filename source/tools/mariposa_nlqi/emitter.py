import sys, os
from rewriter import *

class Emitter(Rewriter):
    def __init__(self, eid, params):
        super().__init__(eid, params)

    def get_temp(self, i):
        return f"temp_{self.eid}_{i}"

    def emit_temp_decls(self, lang):
        if lang == Lang.DAFNY:
            fmt = "\tvar {0} := {1};"
        else:
            assert lang == Lang.VERUS
            fmt = "\tlet {0} = {1};"
        lines = [fmt.format(self.get_temp(0), self.start)]

        for s in self.csteps:
            lines.append(fmt.format(self.get_temp(s.main.id), s.main.result))
        return lines

    def emit_asserts(self, mode, lang):
        lines = self.emit_temp_decls(lang)
        prev = self.get_temp(0)
        for s in self.csteps:
            lines.append("\tassert(" + prev + " == " + self.get_temp(s.main.id) + ") by ")
            prev = self.get_temp(s.main.id)
            lines.append(s.emit_calls(mode) + "// " + str(s.main.id))
        return "\n".join(lines) + "\n"

class ExperimentEmitter:
    def __init__(self, exp_root, params):
        rws = []

        for i in range(params.EXPR_NUM):
            rws.append(Emitter(i, params))

        self.rws = rws
        self.params = params

        if os.path.exists(exp_root):
            os.system(f"rm -rf {exp_root}")
        os.system(f"mkdir {exp_root}")

        self.verus_proj_root = exp_root + "/nlqi_verus"
        self.dafny_proj_root = exp_root + "/nlqi_dafny"

        os.system("cp -r ./tools/mariposa_nlqi/assets/nlqi_verus " + self.verus_proj_root)
        # dafny does not need a main file
        os.system("cp -r ./tools/mariposa_nlqi/assets/nlqi_dafny " + self.dafny_proj_root)

    def get_emitters(self, actual_expr_num=None):
        if actual_expr_num == None:
            actual_expr_num = self.params.EXPR_NUM
        assert actual_expr_num <= self.params.EXPR_NUM
        return self.rws[:actual_expr_num]

    def emit_verus_file(self, mode, actual_expr_num=None):
        out_f = open(f"{self.verus_proj_root}/src/main.rs", "w+")
        out_f.write(VERUS_HEADER)

        rws = self.get_emitters(actual_expr_num)

        for mut_id in range(self.params.MUTANT_NUM):
            if mut_id != 0:
                random.shuffle(rws)

            args = ", ".join([v + ": int" for v in VARS])
            sig = f"pub proof fn {str(mode.value)}_{mut_id}({args})"

            if mode == StepMode.NLA:
                sig += " by (nonlinear_arith)"
            sig += "\n{\n"
            out_f.write(sig)

            for rw in rws:
                out_f.write(rw.emit_asserts(mode, lang=Lang.VERUS))

            out_f.write("\n}\n")

        out_f.write(VERUS_FOOTER)
        out_f.close()

    def get_dafny_file_path(self, mode):
        return f"{self.dafny_proj_root}/{mode.value}.dfy"

    def emit_dafny_file(self, mode, actual_expr_num=0):
        out_f = open(self.get_dafny_file_path(mode), "w+")
        out_f.write(DAFNY_HEADER)
        rws = self.get_emitters(actual_expr_num)

        for mut_id in range(self.params.MUTANT_NUM):
            if mut_id != 0:
                random.shuffle(rws)

            args = ", ".join([v + ": int" for v in VARS])
            sig = f"lemma {str(mode.value)}_{mut_id}({args})"
            sig += "\n{\n"
            out_f.write(sig)

            for rw in rws:
                out_f.write(rw.emit_asserts(mode, lang=Lang.DAFNY))

            out_f.write("\n}\n")
        out_f.close()
 
if __name__ == "__main__":
    if len(sys.argv) == 3:
        ts = int(sys.argv[2])
    else:
        ts = int.from_bytes(os.urandom(8), byteorder="big")

    exp_root = sys.argv[1]
    pa = EmitterParams(ts)
    print(pa, end="")
    ee = ExperimentEmitter(exp_root, pa)

    ee.emit_verus_file(StepMode.AUTO)
    ee.emit_dafny_file(StepMode.AUTO)

#     def emit_as_calc(self, mode, upto, keep_every):
#         csteps = self.get_steps(upto, keep_every)
#         lines = self.emit_temp_variables(csteps)
#         lines.append("\tcalc !{\n\t\t(==)")
#         lines.append("\t\t" + self.emit_temp(0) + ";")
#         for s in csteps:
#             lines.append("\t\t" + s.emit_calls(mode) + "// " + str(s.main.id))
#             lines.append("\t\t" + self.emit_temp(s.main.id) + ";")
#         lines.append("\t}")
#         return "\n".join(lines) + "\n"

#     def emit_as_lemma(self):
#         args = ", ".join([v + ": int" for v in self.vars])
#         lemma = f"""#[verifier::external_body]
# pub proof fn lemma_test_{self.name}()
#     ensures forall |{args}|
#         #[trigger]({self.start})
#         ==
#         #[trigger]({self.steps[len(self.steps) - 1].result})
# """
#         return lemma + "{}\n"
