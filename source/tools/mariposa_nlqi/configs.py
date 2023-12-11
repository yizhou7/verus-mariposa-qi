import random, enum

TERM_VAR_PROB = 0.975
TERM_CONST_PROB = 1 - TERM_VAR_PROB

EARLY_STOP_FACTOR = 0.975

OP_PROB = {
    "+": 0.1,
    "-": 0.1,
    "*": 0.8,
}

DAFNY_BIN_PATH = "~/dafny/dafny"
VREUS_BIN_PATH = "~/verus/source/target-verus/release/verus"

MARIPOSA_ROOT = "~/mariposa/target/release/mariposa"
Z3_BIN_PATH = "~/mariposa/solvers/z3-4.12.2"

VARS = ["a", "b", "c", "d"]

class Lang(enum.Enum):
    VERUS = "verus"
    DAFNY = "dafny"

class StepMode(enum.Enum):
    INST = "inst"
    AUTO = "auto"
    NLA = "nlarith"

class EmitterParams:
    def __init__(self, seed):
        self.STEPS_TOTAL = 8
        self.KEEP_EVERY = 8

        self.EXPR_MAX_DEPTH = 10
        self.EXPR_NUM = 20

        self.MUTANT_NUM = 1
        self.modes = [StepMode.AUTO, StepMode.INST]
        # self.modes = [StepMode.NLA]
        # self.modes = [StepMode.AUTO]

        self.seed = seed
        random.seed(seed)

        self.related = True

        self._LANG_TIMEOUT = 5000 # ms
        self._SMT_TIMEOUT = 10000 # ms

    def get_lang_to_seconds(self):
        assert self._LANG_TIMEOUT > 1000
        return int(self._LANG_TIMEOUT / 1000)

    def get_lang_to_millis(self):
        return self._LANG_TIMEOUT
    
    def get_smt_to_seconds(self):
        assert self._SMT_TIMEOUT > 1000
        return int(self._SMT_TIMEOUT / 1000)

    def get_smt_to_millis(self):
        return self._SMT_TIMEOUT

    def __str__(self):
        return f"""[INFO] total number of rewrite steps: {self.STEPS_TOTAL}
[INFO] keep every (steps): {self.KEEP_EVERY}
[INFO] max depth of expressions: {self.EXPR_MAX_DEPTH}
[INFO] number of expressions: {self.EXPR_NUM}
[INFO] lang timeout (seconds): {self.get_lang_to_seconds()}
[INFO] smt timeout (seconds): {self.get_smt_to_seconds()}
[INFO] solver path: {Z3_BIN_PATH}
[INFO] seed: {self.seed}
"""

VERUS_HEADER = """use builtin_macros::*;
use builtin::*;
mod nl_basics;
use crate::nl_basics::*;
verus! {

"""
VERUS_FOOTER ="""
} // verus!"""

# VERUS_MAIN_HEADER = """
# use builtin_macros::*;

# verus! {

# fn main() { }

# """

DAFNY_HEADER = """include "nl_basics.dfy"

import opened nl_basics
"""