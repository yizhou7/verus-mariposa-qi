from __future__ import annotations

from typing import List, Tuple, Optional, Union, Dict
from dataclasses import dataclass

import re
import os
import argparse
import subprocess

from runner import *


"""
Line number in nl_basic.rs file to the name of the associated manual lemma
"""
LINE_NUM_TO_MANUAL_LEMMA: Dict[int, str] = {
    27: "lemma_add_comm",
    29: "lemma_mul_comm",
    31: "lemma_mul_assoc",
    33: "lemma_mul_dist",
    35: "lemma_mul_dist",
    37: "lemma_mul_dist",
    39: "lemma_mul_dist",
    41: "lemma_mod_mul_noop",
    43: "lemma_mod_mul_noop",
    45: "lemma_mod_mul_noop",
    47: "lemma_mod_mul_vanish",
    49: "lemma_mod_mul_vanish",
    51: "lemma_mod_mul_vanish",
    53: "lemma_mod_add_noop",
    55: "lemma_mod_add_noop",
    57: "lemma_mod_add_noop",
    59: "lemma_mod_sub_noop",
    61: "lemma_mod_sub_noop",
    63: "lemma_mod_sub_noop",
    65: "lemma_eq_ref",
    67: "lemma_eq_sym",
    69: "lemma_eq_trans",
    71: "cong_add_",
    73: "cong_sub_",
    75: "cong_mul_",
    77: "cong_mod_",
}


class AIR:
    class Expr:
        def to_verus_expr(self) -> str:
            raise NotImplementedError()

    @dataclass
    class Apply(Expr):
        name: str
        arguments: List[AIR.Expr]

        def to_verus_expr(self) -> str:
            if self.name == "Poly%main!nl_basics.Elem." or self.name == "%Poly%main!nl_basics.Elem.":
                assert len(self.arguments) == 1
                return self.arguments[0].to_verus_expr()
            
            elif self.name == "main!nl_basics.as_elem.?":
                assert len(self.arguments) == 1
                return f"as_elem({self.arguments[0].to_verus_expr()})"
            
            elif self.name == "I":
                assert len(self.arguments) == 1
                return self.arguments[0].to_verus_expr()

            elif self.name == "main!nl_basics.mul_.?":
                assert len(self.arguments) == 2
                return f"mul_({self.arguments[0].to_verus_expr()}, {self.arguments[1].to_verus_expr()})"
            
            elif self.name == "main!nl_basics.sub_.?":
                assert len(self.arguments) == 2
                return f"sub_({self.arguments[0].to_verus_expr()}, {self.arguments[1].to_verus_expr()})"
            
            elif self.name == "main!nl_basics.add_.?":
                assert len(self.arguments) == 2
                return f"add_({self.arguments[0].to_verus_expr()}, {self.arguments[1].to_verus_expr()})"
            
            elif self.name == "main!nl_basics.mod_.?":
                assert len(self.arguments) == 2
                return f"mod_({self.arguments[0].to_verus_expr()}, {self.arguments[1].to_verus_expr()})"
            
            assert False, f"unknown application name {self.name}"


    @dataclass
    class Variable(Expr):
        name: str

        def to_verus_expr(self) -> str:
            return self.name.split("~")[0]


    @dataclass
    class Const(Expr):
        const: int

        def to_verus_expr(self) -> str:
            return str(self.const)


def parse_air(src: str) -> Union[AIR.Expr, List[AIR.Expr]]:
    """
    Very hacky
    """
    src = re.sub(r"Apply\s*\(", "AIR.Apply(", src)
    src = re.sub(r"Var\s*\(", "AIR.Variable(", src)
    src = re.sub(r"Const\s*\(", "AIR.Const(", src)
    return eval(src)


# @dataclass
# class Source:
#     source: str
#     current_position: int = 0

#     def is_end(self) -> bool:
#         return self.current_position == len(self.source)

#     def parse_whitespace(self) -> Optional[Source]:
#         if self.is_end():
#             return None
        
#         if self.source[self.current_position].isspace():
#             return Source(self.source, self.current_position + 1)

#         return None

#     def parse_whitespaces(self) -> Source:
#         source = self

#         while True:
#             next_source = source.parse_whitespace()
#             if next_source is None:
#                 return source
#             else:
#                 source = next_source

#     def parse_re(self, pattern: str) -> Optional[Tuple[Source, re.Match]]:
#         match = re.search("^" + pattern, self.source[self.current_position:])

#         if match is None:
#             return None
#         else:
#             return Source(self.source, self.current_position + len(match.group(0))), match

#     def parse_str(self, expected_str: str) -> Optional[Source]:
#         if self.current_position + len(expected_str) > len(self.source):
#             return None
 
#         if self.source[self.current_position:self.current_position + len(expected_str)] != expected_str:
#             return None

#         return Source(self.source, self.current_position + len(expected_str))


#     def parse_air_expr(self: Source) -> Optional[Tuple[Source, Tuple[AIRExpr, str]]]:
#         """
#         Parse an AIR expression
#         """

#         self = self.parse_whitespaces()

#         result = self.parse_re(r"Apply\(\"([^\"]*)\"\s*,\s*")
#         if result is not None:
#             self, match = result
#             app_name = match.group(1)

#             result = self.parse_list_air_exprs()
#             if result is not None:
#                 self, arguments = result

#                 self = self.parse_whitespaces()
#                 self = self.parse_str(")")
#                 if self is None:
#                     return None

#                 return self, AIRApplication(app_name, arguments)
            
#         result = self.parse_re(r"Var\(\"([^\"]*)\"\)")
#         if result is not None:
#             self, match = result
#             return self, AIRVariable(match.group(1))

#         return None

#     def parse_list_air_exprs(self: Source) -> Optional[Tuple[Source, Tuple[AIRExpr, ...]]]:
#         """
#         Parse a list of AIR expressions
#         """
        
#         self = self.parse_whitespaces()

#         result = self.parse_str("[")
#         if result is None: return None
#         self = result

#         exprs: List[AIRExpr] = []

#         while True:
#             self = self.parse_whitespaces()

#             result = self.parse_air_expr()
#             if result is None:
#                 result = self.parse_whitespaces().parse_str("]")
#                 if result is None:
#                     return None
#                 else:
#                     return result, tuple(exprs)
            
#             self, expr = result
#             exprs.append(expr)

#             self = self.parse_whitespaces()
#             result = self.parse_str(",")
#             if result is None:
#                 result = self.parse_whitespaces().parse_str("]")
#                 if result is None:
#                     return None
#                 else:
#                     return result, tuple(exprs)
#             else:
#                 self = result



def main():
    # (seed, number of assertions)
    # seeds = [
    #     (1019351439507244526, 25),
    # ]
    seeds: List[Tuple[int, int]] = [
        (10310771465412923117, 93),
        (10773674063941925315, 138),
        (11113478180923454746, 121),
        (11589036378955207294, 110),
        (12977946648451891492, 133),
        (14093723729963449993, 110),
        (14824042700120807701, 123),
        (15167975689647697693, 136),
        (16722714031163977158, 150),
        (16915497189000353100, 110),
        (16986553460063775306, 103),
        (17031248235225517275, 121),
        (17240713826087265239, 142),
        # (17543141536983219972, 133),
        (17959171433899393434, 110),
        (18358992286770131404, 81),
        (2818944399956709518, 133),
        (3003328490971696788, 121),
        (3200963750234244253, 135),
        (3649380853890026228, 110),
        (4999315918640339659, 94),
        (5030692039770373599, 124),
        (5306376619640549961, 163),
        # (5464806266875958074, 94), # timeout
        (5975842660619014552, 148),
        (6016281295233931404, 110),
        (6298502279875071277, 127),
        (6751654071767485075, 121),
        (687115051198467876, 110),
        (7026665295411337406, 144),
        (7676229416794353428, 137),
        (9755754038474804521, 121),
        (9890070528458518474, 108),
    ]

    seeds = seeds[22:]

    parser = argparse.ArgumentParser()
    parser.add_argument("output", help="output directory")

    args = parser.parse_args()

    output_dir = args.output
    failed_dir = os.path.join(output_dir, "failed")

    if not os.path.isdir(output_dir):
        os.mkdir(output_dir)

    if not os.path.isdir(failed_dir):
        os.mkdir(failed_dir)

    for seed_idx, (seed, num_asserts) in enumerate(seeds):
        # mapping from assert(...); to assert() by {}
        assert_replace_map: Dict[str, str] = {}

        for assert_idx in range(num_asserts):
            print(f"### ({seed_idx + 1}/{len(seeds)}) seed {seed} assertion {assert_idx}")

            pa = EmitterParams(seed=seed, config_name="uf")
            er = ExperimentRunner(pa, overwrite=True)
            er.emit_verus_file(StepMode.FREE, actual_expr_num=assert_idx + 1, skip_expr_num=assert_idx)

            emitted_path = f"mariposa_data/uf/{seed}/nlqi_verus/src/main.rs"

            with open(emitted_path) as f:
                match = re.search(r"assert\(.*\);", f.read())
                assert match is not None, f"assertion not found in {emitted_path}"
                assert_stmt_str = match.group(0)

            result = subprocess.run(
                [
                    os.path.expanduser(VREUS_BIN_PATH),
                    "--verify-root",
                    "--crate-type", "lib",
                    "--profile-all",
                    "--log-smt",
                    emitted_path,
                ],
                stdout=subprocess.PIPE,
                stderr=subprocess.PIPE,
            )
            
            if result.returncode != 0:
                print("verus failed")

                # Log verus error
                with open(os.path.join(failed_dir, f"{seed}.{assert_idx}.verus.stderr.txt"), "wb") as f:
                    f.write(result.stderr)
                continue

            stdout = result.stdout.decode()

            # Log used instantiations
            # Format example: instantiations: "/Users/zhengyao/work/verus-mariposa/source/mariposa_data/v_nl/10010383067674129532/nlqi_verus/src/nl_basics.rs:133:9: 134:53 (#0)" inst_main__free_0_12 used: false [Apply("Mul", [Var("d13~112@"), Var("b13~108@")]), Apply("Sub", [Var("c13~110@"), Var("c13~110@")]), Apply("Mul", [Apply("Mul", [Const(87), Var("d13~112@")]), Apply("Add", [Var("a13~106@"), Var("d13~112@")])])]
            
            # with open(os.path.join(output_dir, f"{seed}.{assert_idx}.instantiations.txt"), "w") as f:
            replace_assert_lines = [ f"{assert_stmt_str[:-1]} by {{" ]
            num_used_instantiations = 0
            for match in re.finditer(r"instantiations: \".* (\d+):\d+ \(#\d+\)\" .* used: (true|false) (\[.*\])\n", stdout):
                quantifier_line_num = int(match.group(1))
                used = match.group(2) == "true"
                air_terms = parse_air(match.group(3))

                assert quantifier_line_num in LINE_NUM_TO_MANUAL_LEMMA, \
                       f"cannot find corresponding manual lemma for the quantifier at line {quantifier_line_num}"

                # if used:
                #     print(f"used instantiation: line num {quantifier_line_num}, instances {', '.join([ term.to_verus_expr() for term in air_terms ])}")

                verus_term_strs = []
                for term in air_terms:
                    term_str = term.to_verus_expr()
                    if term_str.startswith("(") and term_str.endswith(")"):
                        term_str = term_str[1:-1]
                    verus_term_strs.append(term_str)

                manual_lemma = LINE_NUM_TO_MANUAL_LEMMA[quantifier_line_num]

                if used:
                    # print(f"used instantiation {manual_lemma}({', '.join(verus_term_strs)})")
                    num_used_instantiations += 1
                    replace_assert_lines.append(f"\t\t{manual_lemma}({', '.join(verus_term_strs)});")
            
            replace_assert_lines.append("\t}")

            if num_used_instantiations != 0:
                assert_replace_map[assert_stmt_str] = "\n".join(replace_assert_lines)

        print(f"### generating instantiated source for seed {seed}")

        pa = EmitterParams(seed=seed, config_name="uf")
        er = ExperimentRunner(pa, overwrite=True)
        er.emit_verus_file(StepMode.FREE, actual_expr_num=num_asserts)

        emitted_path = f"mariposa_data/uf/{seed}/nlqi_verus/src/main.rs"

        with open(emitted_path) as f:
            source = f.read()
            source = re.sub(r"[\t ]*lemma_mul_properties_auto_1\(\);\n", "", source)
            for k, v in assert_replace_map.items():
                source = source.replace(k, v)

        with open(os.path.join(output_dir, f"instantiations-{seed}.rs"), "w") as f:
            f.write(source)

if __name__ == "__main__":
    main()
