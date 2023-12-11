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

def clean_newlines(s):
    return s.replace('\n', ' ').replace('\r', '')

class ExperimentRunner(ExperimentEmitter):
    def __init__(self, proj_root, prams, overwrite=False):
        super().__init__(proj_root, prams, overwrite)
        self.verus_tmp_dir = f"{self.verus_proj_root}/tmp"
        self.dafny_tmp_dir = f"{self.dafny_proj_root}/tmp"

        main_log_path = f"{proj_root}/log.txt"
        if os.path.exists(main_log_path):
            self.log = open(f"{proj_root}/log.txt", "a")
        else:
            self.log = open(f"{proj_root}/log.txt", "w")
            self.log.write(str(prams))

        # this dir is for persistent 
        self.verus_smt_dir = f"{self.verus_proj_root}/log"
        self.dafny_smt_dir = f"{self.dafny_proj_root}/log"

        if not os.path.exists(self.verus_smt_dir):
            os.system(f"mkdir {self.verus_smt_dir}")

        if not os.path.exists(self.verus_tmp_dir):
            os.system(f"mkdir {self.verus_tmp_dir}")
        
        if not os.path.exists(self.dafny_smt_dir):
            os.system(f"mkdir {self.dafny_smt_dir}")

        if not os.path.exists(self.dafny_tmp_dir):
            os.system(f"mkdir {self.dafny_tmp_dir}")

    def log_line(self, line):
        print(line)
        self.log.write(line + "\n")

    def get_smt_file(self, lang, mode, index):
        if lang == Lang.VERUS:
            return f"{self.verus_smt_dir}/{mode.value}_{index}.smt2"
        elif lang == Lang.DAFNY:
            return f"{self.dafny_smt_dir}/{mode.value}_{index}.smt2"

    def get_tmp_file(self, lang, mode=None):
        if lang == Lang.VERUS:
            if mode == StepMode.NLA:
                return f"{self.verus_tmp_dir}/rootmain!{mode.value}_0._01.smt2"
            return f"{self.verus_tmp_dir}/root.smt2"
        elif lang == Lang.DAFNY:
            return f"{self.dafny_tmp_dir}/root.smt2"
    
    def post_process_smt(self, src, dst):
        cmd = [
            MARIPOSA_ROOT,
            f"-i '{src}'",
            f"-o '{dst}'",
            "--chop",
            "--remove-debug"
        ]
        # print(" ".join(cmd))
        # should not take long to split
        stdout, stderr, elapsed = run_command(cmd, 5)
        # we don't expect two split queries
        if not "is split into 1 file(s), ignored 0 check-sat" in stdout:
            self.log_line(clean_newlines(stdout))
        mp_query = dst.replace(".smt2", ".1.smt2")
        assert os.path.exists(mp_query)

    def run_single_verus(self, mode, actual_expr_num):
        verus_file = f"{self.verus_proj_root}/src/main.rs"
        cmd = [
            VREUS_BIN_PATH,
            verus_file,
            f"--verify-root",
            f"--crate-type lib",
            f"--no-auto-recommends-check",
            f"--log smt",
            f"--log-dir {self.verus_tmp_dir}",
            f"--smt-option timeout={self.params.get_lang_to_millis()}"
        ]
        stdout, stderr, elapsed = run_command(cmd, self.params.get_lang_to_seconds() * 2)
        os.system(f"mv {verus_file} {verus_file}.{mode.value}.{actual_expr_num}")
        tmp_file = self.get_tmp_file(Lang.VERUS, mode)
        assert os.path.exists(tmp_file)
        smt_file = self.get_smt_file(Lang.VERUS, mode, actual_expr_num)
        self.post_process_smt(tmp_file, smt_file)
    
        if "verification results:: 1 verified, 0 errors" not in stdout:
            self.log_line("[WARN] verus-tool stdout: " + clean_newlines(stdout))
            self.log_line("[WARN] verus-tool stderr: " + clean_newlines(stderr))
        line = f"[INFO] verus-tool {mode.value} {actual_expr_num} {elapsed}"
        self.log_line(line)
        return elapsed

    def run_verus(self):
        for mode in self.params.modes:
            for i in range(1, self.params.EXPR_NUM):
                self.emit_verus_file(mode, actual_expr_num=i)
                self.run_single_verus(mode, i)

    def run_single_dafny(self, mode, actual_expr_num):
        dafny_file = f"{self.dafny_proj_root}/{mode.value}.dfy"
        tmp_file = self.get_tmp_file(Lang.DAFNY)
        cmd = [
            DAFNY_BIN_PATH,
            dafny_file,
            f"/compile:0",
            f"/timeLimit:{self.params.get_lang_to_seconds()}",
            f"/proverLog:{tmp_file}",
        ]

        # disable NL arith by default
        if mode != StepMode.NLA:
            cmd += [f"/noNLarith"]

        # print(" ".join(cmd))
        stdout, stderr, elapsed = run_command(cmd, self.params.get_lang_to_seconds() * 2)
        assert os.path.exists(tmp_file)
        os.system(f"mv {dafny_file} {dafny_file}.{actual_expr_num}")
        smt_file = self.get_smt_file(Lang.DAFNY, mode, actual_expr_num)
        self.post_process_smt(tmp_file, smt_file)

        if "Dafny program verifier finished with 1 verified, 0 errors" not in stdout:
            self.log_line("[WARN] dafny-tool stdout: " + clean_newlines(stdout))
            self.log_line("[WARN] dafny-tool stderr: " + clean_newlines(stderr))
        self.log_line(f"[INFO] dafny-tool {mode.value} {actual_expr_num} {elapsed}")
        return elapsed

    def run_dafny(self):
        for mode in self.params.modes:
            for i in range(1, self.params.EXPR_NUM):
                self.emit_dafny_file(mode, actual_expr_num=i)
                self.run_single_dafny(mode, i)

    def rerun_smt(self, smt_dir):
        mapped = {i: {} for i in range(1, self.params.EXPR_NUM)}
        for query in list_smt_files(smt_dir):
            query_info = query.split("/")[-1].split(".")[0].split("_")
            assert len(query_info) == 2
            mode, qid = query_info[0], int(query_info[1])
            mapped[qid][mode] = query
        table = [["qid"] + [m for m in self.params.modes]]
        for qid in sorted(mapped):
            row = [qid]
            for m in sorted(mapped[qid]):
                query = mapped[qid][m]
                cmd = [
                    Z3_BIN_PATH,
                    f"{query}",
                    f"-T:{self.params.get_smt_to_seconds()}",
                ]
                stdout, stderr, elapsed = run_command(cmd, self.params.get_smt_to_seconds() + 1)
                self.log_line(f"[INFO] z3 {qid} {m} {elapsed} {query} {clean_newlines(stdout)}")
                row.append(elapsed)
            table.append(row)
        self.log_line(f"[INFO] rerun summary {smt_dir}\n" + tabulate(table))

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
    if len(sys.argv) == 2:
        ts = int(sys.argv[1])
    else:
        ts = int.from_bytes(os.urandom(8), byteorder="big")
    
    exp_root = str(ts)
    pa = EmitterParams(ts)
    print(pa, end="")

    er = ExperimentRunner(exp_root, pa, overwrite=True)
    er.run_verus()
    # er.run_dafny()
    er.rerun_smt(er.verus_smt_dir)
    # er.rerun_smt(er.dafny_smt_dir)
