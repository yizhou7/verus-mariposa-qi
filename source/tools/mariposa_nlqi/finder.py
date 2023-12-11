from runner import *

def find_dafny_unstable(ts, mode):
    exp_root = str(ts)
    pa = EmitterParams(ts)
    pa.STEPS_TOTAL = 1
    pa.KEEP_EVERY = 1

    pa.EXPR_MAX_DEPTH = 6
    pa.EXPR_NUM = 20

    pa.MUTANT_NUM = 1
    pa.modes = [StepMode.NLA]

    pa.related = False
    pa.LANG_TIMEOUT = 5000 
    pa.SMT_TIMEOUT = 10000

    er = ExperimentRunner(exp_root, pa, overwrite=True)

    for i in range(1, er.params.EXPR_NUM):
        er.emit_dafny_file(mode, actual_expr_num=i)
        elapsed = er.run_single_dafny(mode, i)
        if elapsed > pa.get_lang_to_seconds():
            break

    path = er.get_smt_file(Lang.DAFNY, mode, i-1)
    path = path.replace(".smt2", ".1.smt2")
    real_path = os.path.realpath(path)
    er.log_line(f"found potential unstable dafny path: {real_path}")

if __name__ == "__main__":
    if len(sys.argv) == 2:
        ts = int(sys.argv[1])
    else:
        ts = int.from_bytes(os.urandom(8), byteorder="big")
    
    find_dafny_unstable(ts, StepMode.NLA)

