from runner import *

# find dafny query that is unstable under NLA 
# the parameter are set so that it is not too easy or too hard to find
# it is not super reliable, but works most of the time
def find_dafny_unstable(ts):
    StepMode.NLA
    exp_root = f"ah_dafny_unstable/"
    mode = StepMode.NLA
    params = {
        "steps_total": 1,
        "keep_every": 1,
        "expr_max_depth": 4,
        "expr_num": 20,
        "modes": [StepMode.NLA.value],
        "mutant_num": 1,
        "related": False,
        "lang_timeout": 4000,
        "smt_timeout": 10000,
    }

    pa = EmitterParams(params, ts)
    er = ExperimentRunner(exp_root, pa, overwrite=True)

    for i in range(1, er.params.EXPR_NUM):
        er.emit_dafny_file(mode, actual_expr_num=i)
        elapsed = er.run_single_dafny(mode, i)
        if elapsed > pa.get_lang_to_seconds():
            break

    path = er.get_smt_file(Lang.DAFNY, mode, i-1)
    path = path.replace(".smt2", ".1.smt2")
    real_path = os.path.realpath(path)
    assert os.path.exists(real_path)
    er.log_line(f"[INFO] found potential unstable dafny path: {real_path}")

def compare_all_modes_small(ts):
    exp_root = f"ah_6"

    params = {
        "steps_total": 1,
        "keep_every": 1,
        "expr_max_depth": 6,
        "expr_num": 10,
        "modes": [StepMode.INST.value, StepMode.AUTO.value, StepMode.NLA.value, StepMode.FREE.value],
        "mutant_num": 1,
        "related": False,
        "lang_timeout": 5000,
        "smt_timeout": 10000,
    }

    pa = EmitterParams(params, ts)
    er = ExperimentRunner(exp_root, pa, overwrite=True)
    er.run_verus()
    er.run_dafny()
    er.rerun_smt(er.verus_smt_dir)
    er.rerun_smt(er.dafny_smt_dir)

if __name__ == "__main__":
    if len(sys.argv) == 2:
        ts = int(sys.argv[1])
    else:
        ts = int.from_bytes(os.urandom(8), byteorder="big")
    
    # find_dafny_unstable(ts)
    compare_all_modes_small(ts)
