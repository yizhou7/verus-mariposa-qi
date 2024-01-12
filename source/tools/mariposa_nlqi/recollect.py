from __future__ import annotations

from typing import List, Tuple, Optional, Union, Dict
from dataclasses import dataclass

import re
import os
import glob
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
    seeds: List[Tuple[int, int]] = [
        (10039050172752956497, 95),
        (10138268285593698299, 162),
        (10204465944388820460, 110),
        (10277632123461253856, 113),
        (10310771465412923117, 93),
        (10310771465412923117, 93),
        (10341820924366895425, 110),
        (10348695141442659265, 178),
        (10575850319829435039, 110),
        (10701519641660675420, 133),
        (10773674063941925315, 138),
        (10773674063941925315, 138),
        (1085505864101304014, 114),
        (10897712598607272022, 110),
        (10950014827808916131, 135),
        (11113478180923454746, 121),
        (11113478180923454746, 121),
        (11236686781341114412, 133),
        (11451750649442760376, 123),
        (11589036378955207294, 110),
        (11589036378955207294, 110),
        (11705579813100406832, 110),
        (11717138681963207056, 110),
        (11763274574354108152, 110),
        (11842324074847860384, 113),
        (11919816372552329379, 110),
        (12009964388368876333, 121),
        (12446760210054222519, 110),
        (125156815285818513, 110),
        (12674001597599525445, 121),
        (12701927373605284132, 121),
        (12714729563032811592, 95),
        (12747720770740040207, 110),
        (12760110255477418560, 110),
        (12926302432979874879, 137),
        (12977946648451891492, 133),
        (12977946648451891492, 133),
        (13091160074977735895, 110),
        (13222409155834491314, 94),
        (13360697175731502415, 136),
        (13533468192943017227, 102),
        (13535606783997507814, 113),
        (13597416436139611618, 100),
        (13621019901720625584, 93),
        (13927017446441876657, 160),
        (13943722496117901608, 112),
        (14001965942491786517, 121),
        (14093723729963449993, 110),
        (14093723729963449993, 110),
        (14278728475931093849, 91),
        (14569931299192131691, 110),
        (14772869193010499560, 135),
        (14824042700120807701, 123),
        (14824042700120807701, 123),
        (1488535147955003685, 123),
        (14948243698535322488, 79),
        (14991744502867513299, 146),
        (15021100365263232008, 133),
        (15158321600456841551, 112),
        (15167975689647697693, 136),
        (15167975689647697693, 136),
        (15301578142632814295, 110),
        (15358163319403587553, 112),
        (15654302494988248301, 110),
        (15664183534854777800, 110),
        (15685498494321287336, 123),
        (1571068856706693156, 110),
        (1574043633604314753, 133),
        (16061101883533103994, 124),
        (16084621932000428896, 121),
        (1616787912349134171, 110),
        (16406985299524513762, 104),
        (16553746427507147093, 136),
        (16646005180536038664, 102),
        (16699859702613460248, 110),
        (16722714031163977158, 150),
        (16722714031163977158, 150),
        (16810806112738393747, 110),
        (16898795634903054741, 146),
        (16910917439791354243, 110),
        (16913920398920128498, 113),
        (16915497189000353100, 110),
        (16915497189000353100, 110),
        (16947358380715049579, 110),
        (16986553460063775306, 103),
        (16986553460063775306, 103),
        (17031248235225517275, 121),
        (17031248235225517275, 121),
        (17064844892021899953, 93),
        (17240713826087265239, 142),
        (17240713826087265239, 142),
        (17347703109494934576, 93),
        (17420568126143038597, 91),
        (17486477360407479611, 146),
        (17543141536983219972, 133),
        (17543141536983219972, 133),
        (17564161567656738801, 110),
        (17770206951130818096, 110),
        (17821851314737061927, 93),
        (17880933491397050159, 68),
        (17929700153421188318, 125),
        (17959171433899393434, 110),
        (17959171433899393434, 110),
        (1799324072178546074, 95),
        (18061912606703249325, 110),
        (18084258574820078666, 112),
        (18090061279488526001, 113),
        (18168033434807325876, 93),
        (18358992286770131404, 81),
        (18358992286770131404, 81),
        (18425764639971254359, 97),
        (1913902545847172476, 123),
        (2228252222166851158, 125),
        (236007440853171182, 79),
        (2522644944913230816, 148),
        (2523482695495901976, 110),
        (2551691815579040023, 110),
        (2747479176111278198, 110),
        (2818944399956709518, 133),
        (2818944399956709518, 133),
        (2829967645997756309, 146),
        (2890914115091517311, 110),
        (2902215859186306484, 121),
        (2946774963153378453, 148),
        (3003328490971696788, 121),
        (3003328490971696788, 121),
        (3022841509365294092, 180),
        (3075063979775449368, 106),
        (3200963750234244253, 135),
        (3200963750234244253, 135),
        (3237031663676785693, 108),
        (3306180604075339242, 104),
        (3321569325532955074, 112),
        (3417108941994840534, 121),
        (34279984813045682, 108),
        (3525928213266367631, 125),
        (3649380853890026228, 110),
        (3649380853890026228, 110),
        (3705526163519771247, 110),
        (3718548560890062295, 121),
        (3901492184494676344, 110),
        (3918314785490033966, 110),
        (4187210198403575490, 104),
        (4253098293786822454, 110),
        (4342101737032715203, 79),
        (4348342768363055972, 114),
        (4350224400295262088, 113),
        (4394770757777834051, 121),
        (4438573595234441201, 110),
        (4443922990665002599, 135),
        (4851120641566995083, 110),
        (4885230198047943445, 137),
        (4999315918640339659, 94),
        (4999315918640339659, 94),
        (5030692039770373599, 124),
        (5030692039770373599, 124),
        (5064689831912003559, 121),
        (5068701464826966356, 146),
        (5151347673391045034, 123),
        (5306376619640549961, 163),
        (5306376619640549961, 163),
        (5320522158073520270, 110),
        (5361189304363332395, 110),
        (5361353246465579065, 110),
        (5381058492238565541, 80),
        (5464806266875958074, 94),
        (5464806266875958074, 94),
        (5469810957444255771, 110),
        (5586334414592114936, 121),
        (5681840624370880093, 110),
        (5735182439495464284, 110),
        (5859016699225282108, 133),
        (5935564138360947226, 146),
        (5938104413440292428, 112),
        (5965630029537132834, 110),
        (5975842660619014552, 148),
        (5975842660619014552, 148),
        (6016281295233931404, 110),
        (6016281295233931404, 110),
        (6033539793555326100, 123),
        (6042076358693439576, 110),
        (6066673770717959302, 104),
        (6104612831359383870, 121),
        (6117424228796272621, 112),
        (616582296269411225, 116),
        (6177998301280665113, 110),
        (6240373484411627973, 133),
        (6298502279875071277, 127),
        (6298502279875071277, 127),
        (6337704935361624995, 108),
        (643347597933204147, 110),
        (6464245856040048286, 102),
        (6509002135115363253, 110),
        (6546244524730332343, 137),
        (6654906977346840580, 121),
        (6751654071767485075, 121),
        (6751654071767485075, 121),
        (6767683287884060084, 133),
        (687115051198467876, 110),
        (687115051198467876, 110),
        (6982962665832540773, 121),
        (7026665295411337406, 144),
        (7026665295411337406, 144),
        (7243691940338215284, 105),
        (7406928525826627167, 83),
        (7423875262308491534, 110),
        (7455206457819196548, 121),
        (7523176402034188326, 110),
        (7527578629728038303, 86),
        (756731540902202902, 160),
        (7676229416794353428, 137),
        (7676229416794353428, 137),
        (7746001120246472170, 110),
        (7828683074907160794, 110),
        (7861527768692801810, 110),
        (791781860205602141, 104),
        (7921096285139466500, 110),
        (7979261760868816348, 121),
        (799456195662577530, 93),
        (8018915402747649188, 112),
        (8032978187085737583, 112),
        (8099994625102366293, 110),
        (8228520392417247200, 121),
        (8238199863579510514, 110),
        (8375440971751116976, 160),
        (8433838863700444746, 112),
        (8748906386848601453, 150),
        (8793337240211196155, 74),
        (8795715710282645833, 93),
        (8831758969636916559, 165),
        (8855761188861035561, 67),
        (8879238647249529797, 110),
        (8940424532405160017, 110),
        (8979168182955801019, 110),
        (9024156166478412252, 93),
        (9209807454247083532, 110),
        (9308186958259199038, 123),
        (9436611433703036289, 91),
        (9508757297819343831, 123),
        (9755754038474804521, 121),
        (9755754038474804521, 121),
        (9772271436454424834, 163),
        (9888077625435379945, 108),
        (9890070528458518474, 108),
        (9890070528458518474, 108),
        (9933066666367374699, 150),
        (9945793802759130353, 133),
    ]

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

        failed = False

        output_rs_path = os.path.join(output_dir, f"instantiations-{seed}.rs")
        if os.path.isfile(output_rs_path) or len(glob.glob(os.path.join(failed_dir, f"{seed}.*.log"))) != 0:
            print(f"### skipping seed {seed}")
            continue

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

            try:
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
                    stderr=subprocess.STDOUT,
                    timeout=30,
                )

            except subprocess.TimeoutExpired as ex:
                print("verus timed out")
                
                # Log verus error
                with open(os.path.join(failed_dir, f"{seed}.{assert_idx}.verus.timeout.log"), "wb") as f:
                    f.write(ex.stdout)

                failed = True
                break
            
            if result.returncode != 0:
                print("verus failed")

                # Log verus error
                with open(os.path.join(failed_dir, f"{seed}.{assert_idx}.verus.fail.log"), "wb") as f:
                    f.write(result.stdout)

                failed = True
                break

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

        if failed:
            continue

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

        with open(output_rs_path, "w") as f:
            f.write(source)

if __name__ == "__main__":
    main()
