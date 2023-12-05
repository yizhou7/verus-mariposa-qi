from expression import *
from emitter import *
import sys, os
import subprocess, signal, time

def run_command(cmd, timeout):
    cmd = " ".join(cmd)
    # print(f"[INFO] running:\n{cmd}")

    start = time.time()
    sp = subprocess.Popen(cmd, shell=True, 
                            stdout=subprocess.PIPE, 
                            stderr=subprocess.PIPE, 
                            preexec_fn=os.setsid)
    try:
        sp.wait(timeout=timeout)
    except subprocess.TimeoutExpired:
        os.killpg(os.getpgid(sp.pid), signal.SIGKILL)  
        os.killpg(os.getpgid(sp.pid), signal.SIGTERM)  
    elapsed = time.time() - start

    stdout = sp.communicate()[0].decode("utf-8")
    stderr = sp.communicate()[1].decode("utf-8")
    return stdout, stderr, round(elapsed, 2)

def list_smt_files(sub_root):
    file_paths = []
    for root, _, files in os.walk(sub_root):
        for file in files:
            if file.endswith(".smt2"):
                file_paths.append(os.path.join(root, file))
    return file_paths

class ExperimentRunner(ExperimentEmitter):
    def __init__(self, proj_root, prams, overwrite=False):
        super().__init__(proj_root, prams, overwrite)
        # the tmp dir is clear by verus when called
        self.verus_tmp_dir = f"{self.verus_proj_root}/tmp"
        # this dir is for persistent 
        self.verus_smt_dir = f"{self.verus_proj_root}/log"
        self.dafny_smt_dir = f"{self.dafny_proj_root}/log"

        if not os.path.exists(self.verus_smt_dir):
            os.system(f"mkdir {self.verus_smt_dir}")
        
        if not os.path.exists(self.dafny_smt_dir):
            os.system(f"mkdir {self.dafny_smt_dir}")

    def get_verus_smt_file(self, mode, index):
        return f"{self.verus_smt_dir}/{mode.value}_{index}.smt2"

    def get_dafny_smt_file(self, mode, index):
        return f"{self.dafny_smt_dir}/{mode.value}_{index}.smt2"

    def get_verus_tmp_file(self):
        return f"{self.verus_tmp_dir}/root.smt2"
    
    def post_process_smt(self, src, dst):
        cmd = [
            MARIPOSA_ROOT,
            f"-i {src}",
            f"-o {dst}",
            "--chop",
            "--remove-debug"
        ]
        # should not take long to split
        stdout, stderr, elapsed = run_command(cmd, 5)
        # we don't expect two split queries
        assert "is split into 1 file(s), ignored 0 check-sat" in stdout
        mp_query = dst.replace(".smt2", ".1.smt2")
        assert os.path.exists(mp_query)

    def run_single_verus(self, mode, actual_expr_num):
        smt_log_file = self.get_verus_smt_file(mode, actual_expr_num)
        cmd = [
            VREUS_BIN_PATH,
            f"{self.verus_proj_root}/src/main.rs",
            f"--verify-root",
            f"--crate-type lib",
            f"--no-auto-recommends-check",
            f"--log smt",
            f"--log-dir {self.verus_tmp_dir}",
            f"--smt-option timeout={self.params.get_lang_to_millis()}"
        ]
        stdout, stderr, elapsed = run_command(cmd, self.params.get_lang_to_seconds() * 2)
        assert os.path.exists(self.get_verus_tmp_file())
        self.post_process_smt(self.get_verus_tmp_file(), smt_log_file)
    
        verified = False
        if "verification results:: 1 verified, 0 errors" in stdout:
            verified = True
        print(verified, elapsed, actual_expr_num)

    def run_verus(self, mode):
        for i in range(self.params.EXPR_NUM):
            self.emit_verus_file(mode, actual_expr_num=i)
            self.run_single_verus(mode, i)

    def run_single_dafny(self, mode, actual_expr_num):
        smt_log_file = self.get_dafny_smt_file(mode, actual_expr_num)
        cmd = [
            DAFNY_BIN_PATH,
            f"{self.dafny_proj_root}/{mode.value}.dfy",
            f"/compile:0",
            f"/noNLarith",
            f"/timeLimit:{self.params.get_lang_to_seconds()}",
            f"/proverLog:{smt_log_file}",
        ]

        stdout, stderr, elapsed = run_command(cmd, self.params.get_lang_to_seconds() * 2)
        assert os.path.exists(smt_log_file)

        verified = False
        if "Dafny program verifier finished with 1 verified, 0 errors" in stdout:
            verified = True

        print(verified, elapsed, actual_expr_num)

    def run_dafny(self, mode):
        for i in range(1, self.params.EXPR_NUM):
            self.emit_dafny_file(mode, actual_expr_num=i)
            self.run_single_dafny(mode, i)

    def rerun_smt(self, smt_dir):
        mapped = {}
        for query in sorted(list_smt_files(smt_dir)):
            qid = int(query.split("/")[-1].split(".")[0].split("_")[1])
            mapped[qid] = query
        
        for qid in sorted(mapped.keys()):
            query = mapped[qid]
            cmd = [
                Z3_BIN_PATH,
                f"{query}",
                f"-T:{self.params.get_smt_to_seconds() * 4}",
            ]
            # if qid <= 24:
            #     continue
            stdout, stderr, elapsed = run_command(cmd, self.params.get_smt_to_seconds() * 4)
            print(qid, elapsed, stdout.strip())

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

    er = ExperimentRunner(exp_root, pa, True)
    er.run_verus(StepMode.AUTO)
    # er.rerun_smt(er.verus_smt_dir)
    # er.run_dafny(StepMode.AUTO)
