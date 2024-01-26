from runner import *

# find dafny query that is unstable under NLA 
# the parameter are set so that it is not too easy or too hard to find
# it is not super reliable, but works most of the time
# def find_dafny_unstable(ts):
#     nlmode = StepMode.NLA
#     pa = EmitterParams(seed=ts, config_name="dafny_nl_unstable")
#     er = ExperimentRunner(pa, overwrite=True)

#     for i in range(1, er.params.expr_num):
#         er.emit_dafny_file(nlmode, actual_expr_num=i)
#         elapsed = er.run_single_dafny(nlmode, i)
#         if elapsed > pa.get_lang_to_seconds():
#             break

#     path = er.get_smt_file(Lang.DAFNY, nlmode, i-1)
#     path = path.replace(".smt2", ".1.smt2")
#     real_path = os.path.realpath(path)
#     assert os.path.exists(real_path)
#     er.log_line(f"[INFO] found potential unstable dafny path: {real_path}")

def find_verus_uf_unstable(ts, step):
    PA = EmitterParams(seed=ts, config_name="v_nl_2")
    TARGET_SMT_LOWER = 15
    TARGET_SMT_UPPER = 30
    EXPR_NUM_START = 110
    MAX_ITERATIONS = 10

    expr_num = EXPR_NUM_START

    er = ExperimentRunner(PA, overwrite=True)

    if step != 0:
        er.emit_verus_file(StepMode.NLA, actual_expr_num=1)
        _, smt_path, saved_verus = er.run_single_verus(StepMode.NLA, 1)
        return

    iterations = 0
    while iterations < MAX_ITERATIONS:
        er.emit_verus_file(StepMode.AUTO, actual_expr_num=expr_num)
        _, smt_path, saved_verus = er.run_single_verus(StepMode.AUTO, expr_num)
        elapsed, output, _ = run_single_smt(smt_path, TARGET_SMT_UPPER + 5)
        print(f"[INFO] expr_num {expr_num}, elapsed: {elapsed} {output}")

        if expr_num >= PA.expr_num or expr_num <= 0:
            print(f"[INFO] giving up")
            er.clear_experiment()
            return

        if elapsed < TARGET_SMT_LOWER:
            diff = TARGET_SMT_LOWER - elapsed
            if diff < 2:
                expr_num += 2
            else:
                expr_num = int(expr_num * 1.1)
            os.remove(smt_path)
            print(f"[INFO] increasing expr_num to {expr_num}")
        elif elapsed > TARGET_SMT_UPPER:
            diff = elapsed - TARGET_SMT_UPPER
            if diff < 5:
                expr_num -= 2
            else:
                expr_num = int(expr_num * 0.85)
            os.remove(smt_path)
            print(f"[INFO] reducing expr_num to {expr_num}")
        else:
            os.system(f"mv {saved_verus} {er.verus_file}")
            if output != "unsat":
                print(f"[INFO] unexpected output from {er.verus_file}")
                return
            print(f"[INFO] found potential unstable expr_num: {expr_num}")
            print(f"[INFO] smt path {os.path.realpath(smt_path)}")
            break
        iterations += 1

    if iterations == MAX_ITERATIONS:
        print(f"[INFO] giving up")
        er.clear_experiment()
        return

    assert os.path.exists(er.verus_file)

def compare_all_modes(ts, config_name):
    pa = EmitterParams(seed=ts, config_name=config_name)
    er = ExperimentRunner(pa, overwrite=True)
    er.run_default()

if __name__ == "__main__":
    if len(sys.argv) >= 2:
        ts = int(sys.argv[1])
    else:
        ts = int.from_bytes(os.urandom(8), byteorder="big")

    if len(sys.argv) >= 3:
        step = int(sys.argv[2])
    else:
        step = 0

    find_verus_uf_unstable(ts, 1)
    # find_dafny_unstable(ts)
    # compare_all_modes(ts, sys.argv[1])
