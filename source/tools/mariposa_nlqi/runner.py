from expression import *
from emitter import *
import sys, os
import subprocess, signal, time

class ExperimentRunner(ExperimentEmitter):
    def __init__(self, proj_root, prams):
        super().__init__(proj_root, prams)
        # the tmp dir is clear by verus when called
        self.verus_tmp_dir = f"{self.verus_proj_root}/tmp"
        # this dir is for persistent 
        self.verus_smt_dir = f"{self.verus_proj_root}/log"

        if not os.path.exists(self.verus_smt_dir):
            os.system(f"mkdir {self.verus_smt_dir}")

    def get_verus_smt_file(self, mode, index):
        return f"{self.verus_smt_dir}/{mode.value}_{index}.smt2"

    def get_verus_tmp_file(self):
        return f"{self.verus_tmp_dir}/root.smt2"

    def run_single_verus(self):
        cmd = [
            "~/verus/source/target-verus/release/verus",
            f"{self.verus_proj_root}/src/main.rs",
            f"--verify-root",
            f"--crate-type lib",
            f"--log smt",
            f"--log-dir {self.verus_tmp_dir}",
            f"--smt-option timeout={self.params.get_timeout_millis()}"
        ]

        cmd = " ".join(cmd)
        print(f"[INFO] running:\n{cmd}")

        start = time.time()
        sp = subprocess.Popen(cmd, shell=True, 
                              stdout=subprocess.PIPE, 
                              stderr=subprocess.PIPE, 
                              preexec_fn=os.setsid)

        try:
            sp.wait(timeout=self.params.get_timeout_seconds() * 2)
        except subprocess.TimeoutExpired:
            os.killpg(os.getpgid(sp.pid), signal.SIGKILL)  
            os.killpg(os.getpgid(sp.pid), signal.SIGTERM)  
        elapsed = time.time() - start

        stdout = sp.communicate()[0].decode("utf-8")
        stderr = sp.communicate()[1].decode("utf-8")
        assert os.path.exists(self.get_verus_tmp_file())

        if "verification results:: 1 verified, 0 errors" in stdout:
            return True

        return False

    def run_verus(self, mode):
        for i in range(self.params.EXPR_NUM):
            if i != 3:
                continue
            self.emit_verus_file(mode, actual_expr_num=i)
            result = self.run_single_verus()
            smt_log_file = self.get_verus_smt_file(mode, i)
            os.system(f"mv {self.get_verus_tmp_file()} {smt_log_file}")
            print(i, result, smt_log_file)

        # result = self.run_single_verus(mode)
        # smt_log_file = self.get_verus_smt_file(mode)
        # print(result, smt_log_file)

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

if __name__ == "__main__":
    if len(sys.argv) == 3:
        ts = int(sys.argv[2])
    else:
        ts = int.from_bytes(os.urandom(8), byteorder="big")

    exp_root = sys.argv[1]
    exp_root = sys.argv[1]
    pa = EmitterParams(ts)
    print(pa, end="")

    er = ExperimentRunner(exp_root, pa)
    er.run_verus(StepMode.AUTO)

    # if len(sys.argv) == 2:
    #     ts = int(sys.argv[1])
    # else:
    #     ts = int.from_bytes(os.urandom(8), byteorder="big")

    # log_file = open(f"logs.log", "w")
    # log_file.write(str(pa))
    # # print(f"[INFO] init_subexps: {len(init_subexps)}")
    # # log_file.write(f"[INFO] init_subexps: {len(init_subexps)}\n")
    # print(log_file.name)

    # emitters = []

    # for i in range(pa.num_exps):
    #     em = CalcEmitter(str(i), pa)
    #     emitters.append(em)

    # for m in [StepMode.AUTO_ONLY]:
    #     # log_file.write(f"[INFO] {m.value}\n")
    #     # max_step = get_max_calc_steps(em, m, log_file)
    #     emit_verus(emitters, pa, m)
    #     # log_file.write(f"[INFO] mode: {m.value} {max_step}\n")

    # log_file.close()
