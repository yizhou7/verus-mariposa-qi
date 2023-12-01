from expression import *
import sys, os

funs = [lambda e: e.commutative_rewrite(), 
        lambda e: e.associative_rewrite(), 
        lambda e: e.mul_distributive_rewrite(),
        lambda e: e.mul_add_distributive_inverse_rewrite()]

import subprocess, os
import signal

def emit_verus(emitters, mode):
    mod_name = f"calc_{mode.value}"
    
    out_f = open(f"nl_qi_test/src/{mod_name}.rs", "w")
    out_f.write(VERUS_HEADER)

    args = ", ".join([v + ": int" for v in VARS])
    sig = f"pub proof fn lemma_test({args})"
    if mode == StepMode.NL_HINT or mode == StepMode.NL_ONLY:
        sig += " by (nonlinear_arith)"
    out_f.write(sig + " {\n")

    for em in emitters:
        out_f.write(em.emit(mode, upto=2) + "\n")

    out_f.write("\n}\n")
    out_f.write(VERUS_FOOTER)
    out_f.close()

# def run_verus(mode, max_step, exp_depth, i):
#     cmd = f"~/verus/source/target-verus/release/verus ./nl_qi_test/src/main.rs --smt-option solver.timeout=5 --verify-module {mod_name}"
#     print(f"[INFO] running: {cmd}")

#     sp = subprocess.Popen(cmd, shell=True, stdout=subprocess.PIPE, stderr=subprocess.PIPE, preexec_fn=os.setsid)

#     try:
#         sp.wait(timeout=10)
#     except subprocess.TimeoutExpired:
#         os.killpg(os.getpgid(sp.pid), signal.SIGKILL)  
#         os.killpg(os.getpgid(sp.pid), signal.SIGTERM)  

#     # print(f"[INFO] {mode.value} {i} {time.time() - start}")

#     stdout = sp.communicate()[0].decode("utf-8")
#     stderr = sp.communicate()[1].decode("utf-8")

#     if "verification results:: 1 verified, 0 errors" in stdout:
#         return True

#     return False

# def get_max_calc_steps(em, mode, log_file):
#     log_lines = []
    
#     lo, hi = 1, len(em.steps)

#     log_lines.append(f"[DEBUG] emitting upto {hi} steps\n")
#     if run_verus(em, mode, hi):
#         return hi

#     log_lines.append(f"[DEBUG] emitting upto {lo} steps\n")
#     if not run_verus(em, mode, lo):
#         return 0

#     # do binary search
#     while lo < hi:
#         mid = (lo + hi) // 2
#         if run_verus(em, mode, mid):
#             log_lines.append(f"[DEBUG] {mid} success\n")
#             lo = mid + 1
#         else:
#             log_lines.append(f"[DEBUG] {mid} failure\n")
#             hi = mid
#         log_lines.append(f"[DEBUG] new range: {lo} {hi}\n")

#     log_file.writelines(log_lines)

#     return lo - 1

# def mixed_mode_linear_check(em, log_file):
#     log_lines = []

#     for i in range(0, len(em.steps)):
#         log_lines.append(f"[DEBUG] emitting upto {i} steps\n")
#         if run_verus(em, StepMode.STEPPED_INST_AUTO, i):
#             log_lines.append(f"[DEBUG] {i} success\n")
#         else:
#             log_lines.append(f"[DEBUG] {i} failure\n")
#             break

#     log_file.writelines(log_lines)
#     return i+1

class CalcEmitter:
    def __init__(self, max_rewrites, max_depth):
        self.steps = []
        
        retry_count = 0
        retry = True

        while retry:
            self.e = Expression.random_init(max_depth)
            self.init_subexps = self.e.get_unique_subexps()
            self.start = str(self.e)

            for _ in range(max_rewrites):
                nodes = self.e.list_op_nodes()
                random.shuffle(nodes)

                fun = random.choice(funs)

                for n in nodes:
                    call = fun(n)
                    if call != None:
                        cur = str(self.e)
                        self.steps.append((call, cur))
                        break

            if len(self.steps) < max_rewrites:
                retry = True
                self.steps = []
                retry_count += 1
            else:
                retry = False

            if retry_count > 10:
                print("[ERROR] exceeded retry count, decrease max_rewrites or increase max_depth?")
                exit(1)

    def emit(self, mode, skip_every=1, upto=None):
        lines = ["\tcalc !{", "\t\t(==)"]

        if upto == None:
            upto == len(self.steps)
        assert 0 <= skip_every <= upto

        lines.append("\t\t" + self.start + ";")

        for i, s in enumerate(self.steps[:upto]):
            if i % skip_every != 0:
                lines.append("\t\t//\t{" + s[0].emit(mode) + "}\t//\t" + str(i))
                lines.append("\t\t//" + s[1] + ";")
            else:
                lines.append("\t\t\t{" + s[0].emit(mode) + "}\t// " + str(i))
                lines.append("\t\t" + s[1] + ";")
        lines.append("\t}")
        return "\n".join(lines)

    def emit_asserts(self, mode, skip_every=1, upto=None):
        if mode == StepMode.STEPPED_INST_AUTO:
            return self.emit_asserts_mixed(upto)

        if upto == None:
            upto == len(self.steps)
        assert 0 <= skip_every <= upto

        lines = [f"\t\tlet temp_0 = {self.start};"]

        for i, s in enumerate(self.steps[:upto]):
            lines.append(f"\t\tlet temp_{i+1} = {s[1]};")

        for i, s in enumerate(self.steps[:upto]):
            if i % skip_every != 0:
                lines.append("\t\t//\t{" + s[0].emit(mode) + "}\t//\t" + str(i))
                lines.append("\t\t//temp_" + str(i) + ";")
            else:
                lines.append(f"\t\tassert(temp_{i} == temp_{i+1}) by ")
                lines.append("\t\t\t{" + s[0].emit(mode) + "}\t// " + str(i))

        return "\n".join(lines)

    def emit_asserts_mixed(self, split):
        assert 0 <= split < len(self.steps)

        lines = [f"\t\tlet temp_0 = {self.start};"]

        for i, s in enumerate(self.steps[:split+1]):
            lines.append(f"\t\tlet temp_{i+1} = {s[1]};")

        for i, s in enumerate(self.steps[:split]):
            lines.append(f"\t\tassert(temp_{i} == temp_{i+1}) by ")
            lines.append("\t\t\t{" + s[0].emit(StepMode.INST_ONLY) + "}\t// " + str(i))

        i = split
        lines.append(f"\t\tassert(temp_{i} == temp_{i+1}) by ")
        lines.append("\t\t\t{" + s[0].emit(StepMode.AUTO_ONLY) + "}\t// " + str(i))

        return "\n".join(lines)

VERUS_HEADER = """use builtin_macros::*;
use builtin::*;
use vstd::calc_macro::*;
use crate::nl_basics::*;
verus! {

"""

VERUS_FOOTER ="""} // verus!"""

if __name__ == "__main__":
    max_step = int(sys.argv[1])
    exp_depth = int(sys.argv[2])

    if len(sys.argv) == 4:
        ts = int(sys.argv[3])
    else:
        ts = int.from_bytes(os.urandom(8), byteorder="big")
    random.seed(ts)

    log_file = open(f"logs/{max_step}_{exp_depth}_{ts}.log", "w")
    log_file.write(f"[INFO] max_step: {max_step}\n")
    log_file.write(f"[INFO] exp_depth: {exp_depth}\n")
    log_file.write(f"[INFO] seed: {ts}\n")
    # print(f"[INFO] init_subexps: {len(init_subexps)}")
    # log_file.write(f"[INFO] init_subexps: {len(init_subexps)}\n")
    print(log_file.name)

    emitters = []
    for i in range(10):
        em = CalcEmitter(max_step, exp_depth)
        emitters.append(em)

    for m in [StepMode.INST_ONLY, StepMode.AUTO_ONLY]:
        # log_file.write(f"[INFO] {m.value}\n")
        # max_step = get_max_calc_steps(em, m, log_file)
        emit_verus(emitters, m)

        print(f"[INFO] {m.value} {max_step}")
        log_file.write(f"[INFO] mode: {m.value} {max_step}\n")

    log_file.close()
