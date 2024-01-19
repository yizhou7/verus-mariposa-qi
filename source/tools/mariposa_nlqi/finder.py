from runner import *

# find dafny query that is unstable under NLA 
# the parameter are set so that it is not too easy or too hard to find
# it is not super reliable, but works most of the time
def find_dafny_unstable(ts):
    nlmode = StepMode.NLA
    pa = EmitterParams(seed=ts, config_name="dafny_nl_unstable")
    er = ExperimentRunner(pa, overwrite=True)

    for i in range(1, er.params.expr_num):
        er.emit_dafny_file(nlmode, actual_expr_num=i)
        elapsed = er.run_single_dafny(nlmode, i)
        if elapsed > pa.get_lang_to_seconds():
            break

    path = er.get_smt_file(Lang.DAFNY, nlmode, i-1)
    path = path.replace(".smt2", ".1.smt2")
    real_path = os.path.realpath(path)
    assert os.path.exists(real_path)
    er.log_line(f"[INFO] found potential unstable dafny path: {real_path}")

def find_verus_unstable(ts, find=0):
    nlmode = StepMode.NLA
    instmode = StepMode.INST
    pa = EmitterParams(seed=ts, config_name="v_nl_2")
    er = ExperimentRunner(pa, overwrite=True)

    if find == 0:
        for i in range(1, er.params.expr_num):
            er.emit_verus_file(nlmode, actual_expr_num=i)
            elapsed, saved_auto_file = er.run_single_verus(nlmode, i)
            path = er.get_smt_file(Lang.VERUS, nlmode, i)
            path = path.replace(".smt2", ".1.smt2")
            real_path = os.path.realpath(path)
            os.system("rm " + real_path)
            os.system("rm " + saved_auto_file)

            if elapsed > pa.get_lang_to_seconds():
                find = i -1
                break

        if find == 0:
            er.clear()
            print("[INFO] not found")
            return

    for mode in [StepMode.NLA, StepMode.INST, StepMode.AUTO]:
        er.emit_verus_file(mode, actual_expr_num=find)
        elapsed, saved_src_file = er.run_single_verus(mode, find)
        query_path = er.get_smt_file(Lang.VERUS, mode, find)
        query_path = os.path.realpath(query_path.replace(".smt2", ".1.smt2"))
        er.log_line(f"[INFO] {mode} path: {query_path}")

    os.system(f"mv {saved_src_file} {er.verus_file}")
    er.log_line(f"[INFO] found potential unstable verus query")

def compare_all_modes(ts, config_name):
    pa = EmitterParams(seed=ts, config_name=config_name)
    er = ExperimentRunner(pa, overwrite=True)
    er.run_default()

if __name__ == "__main__":
    if len(sys.argv) >= 2:
        ts = int(sys.argv[1])
    else:
        ts = int.from_bytes(os.urandom(8), byteorder="big")

    if len(sys.argv) == 3:
        find = int(sys.argv[2])
    else:
        find = 0

    print(f"[INFO] seed: {ts} {find}")
    find_verus_unstable(ts, find)
    # compare_all_modes(ts, sys.argv[1])
