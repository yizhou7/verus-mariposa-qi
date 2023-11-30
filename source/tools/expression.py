import random
import enum
import os
# from basic_utils import *

VAR_PROB = 0.95

VARS = ["a", "b", "c"]

def rconst():
    return f"({int(random.random()*100)} as int)"

class Operator(enum.Enum):
    ADD = "+"
    SUB = "-"
    MUL = "*"
    
    def new():
        r = random.random()
        if r <= OP_PROB[Operator.ADD]:
            return Operator.ADD
        elif r <= OP_PROB[Operator.ADD] + OP_PROB[Operator.SUB]:
            return Operator.SUB
        else:
            return Operator.MUL

OP_PROB = {
    Operator.ADD: 0.1,
    Operator.SUB: 0.1,
    Operator.MUL: 0.8,
}

class Mode(enum.Enum):
    INST_HINT = "inst_hint"
    INST_ONLY = "inst_only"
    AUTO_HINT = "auto_hint"
    AUTO_ONLY = "auto_only"
    NL_HINT = "nl_arith_hint"
    NL_ONLY = "nl_arith_only"
    STEPPED_INST_AUTO = "stepped_inst_auto"

class LemmaCall:
    def __init__(self, name, args):
        self.name = name
        self.args = args
        
        self.inst_call = "lemma_%s(%s);" % (self.name, ", ".join([str(a) for a in self.args]))
        self.auto_call = "lemma_mul_properties_auto(); "
        self.hint_call = None

    def set_hint(self, left, right):
        self.hint_call = "assert (%s == %s)" % (left, right)

    def emit(self, mode):
        if mode == Mode.AUTO_ONLY: 
            return self.auto_call

        if mode == Mode.NL_ONLY:
            return ""

        if mode == Mode.INST_ONLY:
            return self.inst_call

        if mode == Mode.INST_HINT:
            return self.inst_call + " " + self.hint_call

        assert self.hint_call != None

        if mode == Mode.AUTO_HINT:
            return self.hint_call + " by {" + self.auto_call + "}"

        if mode == Mode.NL_HINT:
            return self.hint_call

        assert False

def pick_side(left, right):
    if left and right:
        if random.random() < 0.5:
            left = False
        else:
            right = False
    assert left + right <= 1
    return left, right

import math

class Expression:
    def __init__(self, op, left, right):
        self.op = op

        if op == None:
            if random.random() <= VAR_PROB:
                self.value = random.choice(VARS)
            else:
                self.value = rconst()
        else:
            self.value = None

        self.left = left
        self.right = right

    @classmethod
    def random_init(cls, max_depth, prob=1):
        op = Operator.new()
        # may randomly choose to stop at depth larger than 1
        if random.random() > prob or max_depth == 0:
            left, right, op = None, None, None
        else:
            left = Expression.random_init(max_depth-1, prob*0.95)
            right = Expression.random_init(max_depth-1, prob*0.95)
        return cls(op, left, right)

    def get_layer_stats(self, depth=0):
        if self.op == None:
            return {depth: 1}
        else:
            left_stats = self.left.get_layer_stats(depth+1)
            right_stats = self.right.get_layer_stats(depth+1)
            for k in right_stats:
                if k in left_stats:
                    left_stats[k] += right_stats[k]
                else:
                    left_stats[k] = right_stats[k]
            left_stats[depth] = 1
            return left_stats

    def list_op_nodes(self):
        if self.op == None:
            return []
        else:
            return [self] + self.left.list_op_nodes() + self.right.list_op_nodes()

    def associative_rewrite(self):
        call = None

        if self.op != Operator.MUL:
            return call

        left_enable, right_enable = pick_side(self.left.op == self.op, 
                                            self.right.op == self.op)

        orig = str(self)

        if left_enable:
            call = LemmaCall("mul_is_associative", [self.left.left, self.left.right, self.right])
            t_left = self.left
            self.left = t_left.left
            self.right = Expression(self.op, t_left.right, self.right)
            call.set_hint(orig, str(self))

        if right_enable:
            call = LemmaCall("mul_is_associative", [self.left, self.right.left, self.right.right])
            t_right = self.right
            self.right = t_right.right
            self.left = Expression(self.op, self.left, t_right.left)
            call.set_hint(orig, str(self))

        return call
    
    def commutative_rewrite(self):
        if self.op != Operator.MUL:
            return None
        orig = str(self)
        call = LemmaCall("mul_is_commutative", [self.left, self.right])
        t_right, t_left = self.right, self.left
        self.left, self.right = t_right, t_left
        call.set_hint(orig, str(self))
        return call

    def mul_distributive_rewrite(self):
        call = None

        if self.op != Operator.MUL:
            return call

        left_enable, right_enable = pick_side(self.left.op in {Operator.ADD, Operator.SUB},
                                            self.right.op in {Operator.ADD, Operator.SUB})

        orig = str(self)

        t_right, t_left = self.right, self.left

        if left_enable:
            call =  LemmaCall("mul_is_distributive", [self.left.left, self.left.right, self.right])
            op = self.left.op
            self.left = Expression(Operator.MUL, t_left.left, t_right)
            self.right = Expression(Operator.MUL, t_left.right, t_right)
            self.op = op
            call.set_hint(orig, str(self))

        if right_enable:
            call =  LemmaCall("mul_is_distributive", [self.left, self.right.left, self.right.right])
            op = self.right.op
            self.left = Expression(Operator.MUL, t_left, t_right.left)
            self.right = Expression(Operator.MUL, t_left, t_right.right)
            self.op = op
            call.set_hint(orig, str(self))

        return call

    def mul_add_distributive_inverse_rewrite(self):
        call = None
    
        if self.left.op != Operator.MUL or \
            self.right.op != Operator.MUL:
            return call
        
        if self.op not in {Operator.ADD, Operator.SUB}:
            return call

        left_enable, right_enable = pick_side(str(self.left.left) == str(self.right.left),
                                            str(self.left.right) == str(self.right.right))

        t_right, t_left = self.right, self.left

        orig = str(self)
        op = self.op

        if left_enable:
            x, y, z = t_left.left, t_left.right, t_right.right
            call =  LemmaCall("mul_is_distributive", [x, y, z])
            self.left = x
            self.right = Expression(op, y, z)
            self.op = Operator.MUL
            call.set_hint(orig, str(self))

        if right_enable:
            x, y, z = t_left.left, t_right.left, t_right.right
            call =  LemmaCall("mul_is_distributive", [x, y, z])
            self.left = Expression(op, x, y)
            self.right = z
            self.op = Operator.MUL
            call.set_hint(orig, str(self))

        return call

    def __str__(self):
        if self.op == None:
            return str(self.value)
        return "(%s%s%s)" % (self.left, self.op.value, self.right)

funs = [
        lambda e: e.commutative_rewrite(), 
        lambda e: e.associative_rewrite(), 
        lambda e: e.mul_distributive_rewrite(),
        lambda e: e.mul_add_distributive_inverse_rewrite()]

class CalcEmitter:
    def __init__(self, name, max_rewrites, max_depth):
        self.steps = []
        self.name = name
        
        retry_count = 0
        retry = True

        while retry:
            self.e = Expression.random_init(max_depth)
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

            print(f"[INFO] gen steps {len(self.steps)}/{max_rewrites}")

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
        if mode == Mode.STEPPED_INST_AUTO:
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
            lines.append("\t\t\t{" + s[0].emit(Mode.INST_ONLY) + "}\t// " + str(i))

        i = split
        lines.append(f"\t\tassert(temp_{i} == temp_{i+1}) by ")
        lines.append("\t\t\t{" + s[0].emit(Mode.AUTO_ONLY) + "}\t// " + str(i))
        
        return "\n".join(lines)

VERUS_HEADER = """use builtin_macros::*;
use builtin::*;
use vstd::calc_macro::*;
use crate::nl_basics::*;
verus! {

"""

VERUS_FOOTER ="""} // verus!"""

import subprocess, os
import signal, time

def run_verus(em, mode, i):
    mod_name = f"calc_{mode.value}"
    
    out_f = open(f"nl_qi_test/src/{mod_name}.rs", "w")
    out_f.write(VERUS_HEADER)

    args = ", ".join([v + ": int" for v in VARS])
    sig = f"pub proof fn lemma_test({args})"
    if mode == Mode.NL_HINT or mode == Mode.NL_ONLY:
        sig += " by (nonlinear_arith)"
    out_f.write(sig + " {\n")

    out_f.write(em.emit_asserts(mode, upto=i))

    out_f.write("\n}\n")
    out_f.write(VERUS_FOOTER)
    out_f.close()

    cmd = f"~/verus/source/target-verus/release/verus ./nl_qi_test/src/main.rs --verify-module {mod_name}"
    print(f"[INFO] running: {cmd}")
    # start = time.time()

    sp = subprocess.Popen(cmd, shell=True, stdout=subprocess.PIPE, stderr=subprocess.PIPE, preexec_fn=os.setsid)
    
    try:
        sp.wait(timeout=5)
    except subprocess.TimeoutExpired:
        os.killpg(os.getpgid(sp.pid), signal.SIGKILL)  
        os.killpg(os.getpgid(sp.pid), signal.SIGTERM)  

    # print(f"[INFO] {mode.value} {i} {time.time() - start}")

    stdout = sp.communicate()[0].decode("utf-8")
    stderr = sp.communicate()[1].decode("utf-8")

    if "verification results:: 1 verified, 0 errors" in stdout:
        return True

    return False

def get_max_calc_steps(em, mode, log_file):
    log_lines = []
    
    lo, hi = 1, len(em.steps)

    log_lines.append(f"[DEBUG] emitting upto {hi} steps\n")
    if run_verus(em, mode, hi):
        return hi

    log_lines.append(f"[DEBUG] emitting upto {lo} steps\n")
    if not run_verus(em, mode, lo):
        return 0

    # do binary search
    while lo < hi:
        mid = (lo + hi) // 2
        if run_verus(em, mode, mid):
            log_lines.append(f"[DEBUG] {mid} success\n")
            lo = mid + 1
        else:
            log_lines.append(f"[DEBUG] {mid} failure\n")
            hi = mid
        log_lines.append(f"[DEBUG] new range: {lo} {hi}\n")

    log_file.writelines(log_lines)

    return lo - 1

def mixed_mode_linear_check(em, log_file):
    log_lines = []

    for i in range(0, len(em.steps)):
        log_lines.append(f"[DEBUG] emitting upto {i} steps\n")
        if run_verus(em, Mode.STEPPED_INST_AUTO, i):
            log_lines.append(f"[DEBUG] {i} success\n")
        else:
            log_lines.append(f"[DEBUG] {i} failure\n")
            break

    log_file.writelines(log_lines)
    return i+1

import sys

if __name__ == "__main__":
    ts = int.from_bytes(os.urandom(8), byteorder="big")
    # ts = 15517451473674460574
    random.seed(ts)

    # e = Expression.random_init(10)
    # layers = e.get_layer_stats()
    # for depth in sorted(layers):
    #     print(depth, round(layers[depth]/ 2 ** depth, 2))

    max_step = int(sys.argv[1])
    max_depth = int(sys.argv[2])

    em = CalcEmitter(0, max_step, max_depth)
    log_file = open(f"logs/{max_step}_{max_depth}_{ts}.log", "w")
    print(log_file.name)
    # count = mixed_mode_linear_check(em, log_file)
    # print(f"[INFO] {ts} {Mode.STEPPED_INST_AUTO.value} {count}/{len(em.steps)}")
    # log_file.write(f"[INFO] {ts} {Mode.STEPPED_INST_AUTO.value} {count}/{len(em.steps)}")

    for m in [Mode.NL_ONLY, Mode.AUTO_ONLY, Mode.INST_ONLY]:
    # for m in [Mode.INST_ONLY]:
        log_file.write(f"[INFO] {ts} {m.value}\n")
        max_step = get_max_calc_steps(em, m, log_file)
        print(f"[INFO] {ts} {m.value} {max_step}/{len(em.steps)}")
        log_file.write(f"[INFO] {ts} {m.value} {max_step}/{len(em.steps)}\n")

    log_file.close()
