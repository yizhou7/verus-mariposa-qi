import sys, os
from rewriter import *
from axioms import *

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
            if mode == StepMode.LBL:
                if lang == Lang.DAFNY:
                    lines.append(f"\tlabel lbl_{self.eid}: ")
                else:
                    assert lang == Lang.VERUS
                    lines.append("\tassert (true) by {")

            # stmt = f"\tassert(eq_({prev}, {self.get_temp(s.main.id)}))"
            stmt = f"\tassert({prev} == {self.get_temp(s.main.id)})"
            if mode == StepMode.NLA or mode == StepMode.FREE:
                lines.append(stmt + ";")
            else:
                lines.append(stmt + " by ")
                prev = self.get_temp(s.main.id)
                lines.append(s.emit_calls(mode) + "// " + str(s.main.id))

            if mode == StepMode.LBL and lang == Lang.VERUS:
                lines.append("\t}")
        return "\n".join(lines) + "\n"

class ProjectEmitter:
    def __init__(self, proj_root, params, overwrite=False):
        rws = []

        for i in range(params.expr_num):
            em = Emitter(i, params)
            if not em.ok:
                print(f"[ERROR] failed to generate expression {i}, exiting.")
                exit(1)
            rws.append(em)

        self.rws = rws
        self.params = params

        self.verus_proj_root = proj_root + "/nlqi_verus"
        self.dafny_proj_root = proj_root + "/nlqi_dafny"

        if os.path.exists(proj_root):
            if not overwrite:
                print(f"[INFO] {proj_root} already exists, not overwriting.")
                return
            print(f"[INFO] {proj_root} already exists, overwriting.")
            os.system(f"rm -rf {proj_root}")

        os.system(f"mkdir {proj_root}")
        os.system("cp -r ./tools/mariposa_nlqi/assets/nlqi_verus " + self.verus_proj_root)
        # dafny does not need a main file
        os.system("cp -r ./tools/mariposa_nlqi/assets/nlqi_dafny " + self.dafny_proj_root)

    def get_emitters(self, actual_expr_num=None, skip_expr_num=None):
        if actual_expr_num == None:
            actual_expr_num = self.params.expr_num
        assert actual_expr_num <= self.params.expr_num
        if skip_expr_num is None:
            skip_expr_num = 0
        return self.rws[skip_expr_num:actual_expr_num]
    
    def get_args(self):
        args = []
        if self.params.related:
            args = ", ".join([f"{v}: Elem" for v in VARS + ["m"]])
        else:
            for i in range(self.params.expr_num):
                args += [", ".join([f"{v}{i}: Elem" for v in VARS + ["m"]])]
            args = ",\n".join(args)
        return args

    def emit_verus_file(self, mode, actual_expr_num=None, skip_expr_num=None):
        out_f = open(f"{self.verus_proj_root}/src/main.rs", "w+")
        out_f.write(VERUS_HEADER)

        rws = self.get_emitters(actual_expr_num, skip_expr_num)

        for mut_id in range(self.params.mutant_num):
            if mut_id != 0:
                random.shuffle(rws)
            args = self.get_args()
            sig = f"pub proof fn {str(mode.value)}_{mut_id}({args})"
            sig += "\nrequires m != 0"

            # if mode == StepMode.NLA:
            #     sig += " by (nonlinear_arith)"
            sig += "\n{\n"
            out_f.write(sig)

            if mode == StepMode.FREE:
                out_f.write(f"\t{AUTO_CALL};\n")

            for rw in rws:
                out_f.write(rw.emit_asserts(mode, lang=Lang.VERUS))

            out_f.write("\n}\n")

        out_f.write(VERUS_FOOTER)
        out_f.close()

    def get_dafny_file_path(self, mode):
        return f"{self.dafny_proj_root}/{mode.value}.dfy"

    def emit_dafny_file(self, mode, actual_expr_num=None):
        out_f = open(self.get_dafny_file_path(mode), "w+")
        out_f.write(DAFNY_HEADER)
        rws = self.get_emitters(actual_expr_num)

        for mut_id in range(self.params.mutant_num):
            if mut_id != 0:
                random.shuffle(rws)
            args = self.get_args()
            sig = f"lemma {str(mode.value)}_{mut_id}({args})"
            sig += "\n{\n"
            out_f.write(sig)

            if mode == StepMode.FREE:
                out_f.write(f"\t{AUTO_CALL};\n")

            for rw in rws:
                out_f.write(rw.emit_asserts(mode, lang=Lang.DAFNY))

            out_f.write("\n}\n")
        out_f.close()
 
if __name__ == "__main__":
    if len(sys.argv) == 3:
        ts = int(sys.argv[2])
    else:
        ts = int.from_bytes(os.urandom(8), byteorder="big")

    proj_root = str(ts)
    pa = EmitterParams(ts, config_name=sys.argv[1])
    print(pa, end="")
    ee = ProjectEmitter(proj_root, pa, overwrite=True)
    # ee.emit_dafny_file(StepMode.LBL)
    ee.emit_verus_file(StepMode.AUTO)
    # ee.emit_verus_file(StepMode.INST)
    print(f"[INFO] debug:")
    cmd = f"~/verus-mariposa-qi/source/target-verus/release/verus --crate-type lib --verify-root {proj_root}/nlqi_verus/src/main.rs --log smt --rlimit 100"
    os.system(cmd)
    print(cmd)
