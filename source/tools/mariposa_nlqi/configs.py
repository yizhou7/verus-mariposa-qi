import random, enum, json

TERM_VAR_PROB = 0.975
TERM_CONST_PROB = 1 - TERM_VAR_PROB

EARLY_STOP_FACTOR = 0.975


DAFNY_BIN_PATH = "~/dafny/dafny"
VREUS_BIN_PATH = "~/verus/source/target-verus/release/verus"

MARIPOSA_ROOT = "~/mariposa/target/release/mariposa"
Z3_BIN_PATH = "~/mariposa/solvers/z3-4.12.2"

VARS = ["a", "b", "c", "d"]

AUTO_CALL = "lemma_mul_properties_auto_1()"

class Lang(enum.Enum):
    VERUS = "verus"
    DAFNY = "dafny"

class StepMode(enum.Enum):
    INST = "inst"
    AUTO = "auto"
    NLA = "nlarith"
    FREE = "free"
    LBL = "label"

class EmitterParams:
    def __init__(self, seed, config_name="default"):
        config_path = f"tools/mariposa_nlqi/configs/{config_name}.json"
        contents = json.load(open(config_path, "r"))

        self.root_dir = contents["root_dir"]
        self.steps_total = contents["steps_total"]
        self.keep_every = contents["keep_every"]
        self.short_cut = contents["short_cut"]

        self.expr_max_depth = contents["expr_max_depth"]
        self.expr_num = contents["expr_num"]

        self.modes = [StepMode(i) for i in contents["modes"]]

        self.related = contents["related"]
        self.mutant_num = contents["mutant_num"]

        self.langs = [Lang(i) for i in contents["langs"]]
        self.lang_timeout = contents["lang_timeout"] # seconds
        self.smt_timeout = contents["smt_timeout"] # seconds

        self.seed = seed
        random.seed(seed)

    def get_lang_to_seconds(self):
        assert self.lang_timeout < 1000
        return self.lang_timeout

    def get_lang_to_millis(self):
        return self.lang_timeout * 1000
    
    def get_smt_to_seconds(self):
        assert self.smt_timeout < 1000
        return int(self.smt_timeout)

    def get_smt_to_millis(self):
        return self.smt_timeout * 1000

    def __str__(self):
        return f"""[INFO] total number of rewrite steps: {self.steps_total}
[INFO] keep every (steps): {self.keep_every}
[INFO] max depth of expressions: {self.expr_max_depth}
[INFO] number of expressions: {self.expr_num}
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