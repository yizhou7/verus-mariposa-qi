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

def emit_verus_file(proj_root, mode, rws):
    mod_name = f"{mode.value}"
    out_f = open(f"{proj_root}/src/{mod_name}.rs", "w+")
    out_f.write(VERUS_HEADER)

    for mut_id in range(pa.MUTANT_NUM):
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

def emit_verus_main(proj_root, prams):
    out_f = open(f"{proj_root}/src/main.rs", "w+")
    header = ""

    for m in prams.modes:
        header += f"mod {m.value};\n"

    out_f.write(header + VERUS_MAIN_HEADER)
    out_f.write(VERUS_FOOTER)
    out_f.close()

def emit_dafny_file(proj_root, mode, rws):
    mod_name = f"{mode.value}"
    out_f = open(f"{proj_root}/{mod_name}.dfy", "w+")
    out_f.write(DAFNY_HEADER)

    for mut_id in range(pa.MUTANT_NUM):
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

def emit_verus_project(proj_root, prams, rws):
    proj_root = proj_root + "/nlqi_verus"
    os.system("cp -r ./tools/mariposa_nlqi/assets/nlqi_verus " + proj_root)
    emit_verus_main(proj_root, prams)

    for m in pa.modes:
        emit_verus_file(proj_root, m, rws)

def emit_dafny_project(proj_root, prams, rws):
    proj_root = proj_root + "/nlqi_dafny"
    os.system("cp -r ./tools/mariposa_nlqi/assets/nlqi_dafny " + proj_root)

    for m in pa.modes:
        emit_dafny_file(proj_root, m, rws)

if __name__ == "__main__":
    if len(sys.argv) == 3:
        ts = int(sys.argv[2])
    else:
        ts = int.from_bytes(os.urandom(8), byteorder="big")

    pa = EmitterParams(ts)
    print(pa, end="")

    rws = []
    for i in range(pa.EXPR_NUM):
        rws.append(Emitter(i, pa))

    exp_root = sys.argv[1]
    if os.path.exists(exp_root):
        os.system(f"rm -rf {exp_root}")
    os.system(f"mkdir {exp_root}")

    emit_verus_project(exp_root, pa, rws)
    emit_dafny_project(exp_root, pa, rws)

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