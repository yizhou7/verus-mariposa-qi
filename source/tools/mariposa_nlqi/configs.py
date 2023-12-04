import random, enum

TERM_VAR_PROB = 0.975
TERM_CONST_PROB = 1 - TERM_VAR_PROB

EARLY_STOP_FACTOR = 0.975

OP_PROB = {
    "+": 0.1,
    "-": 0.1,
    "*": 0.8,
}

VARS = ["a", "b", "c", "d"]

class Lang(enum.Enum):
    VERUS = "verus"
    DAFNY = "dafny"

class StepMode(enum.Enum):
    INST = "inst"
    AUTO = "auto"
    NLA = "nl_arith"

class EmitterParams:
    def __init__(self, seed):
        self.LANG = Lang.VERUS

        self.STEPS_TOTAL = 1
        self.KEEP_EVERY = 1

        self.EXPR_MAX_DEPTH = 2
        self.EXPR_NUM = 3

        self.MUTANT_NUM = 1
        self.modes = [StepMode.AUTO, StepMode.INST]

        self.seed = seed
        random.seed(seed)

    def __str__(self):
        return f"""[INFO] language: {self.LANG.value}
[INFO] total number of rewrite steps: {self.STEPS_TOTAL}
[INFO] max depth of expressions: {self.EXPR_MAX_DEPTH}
[INFO] number of expressions: {self.EXPR_NUM}
[INFO] keep every: {self.KEEP_EVERY}
[INFO] seed: {self.seed}
"""

VERUS_HEADER = """use builtin_macros::*;
use builtin::*;
use crate::nl_basics::*;
verus! {

"""
VERUS_FOOTER ="""} // verus!"""

VERUS_MAIN_HEADER = """
use builtin_macros::*;
mod nl_basics;

verus! {

fn main() { }

"""