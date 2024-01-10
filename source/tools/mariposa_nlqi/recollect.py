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
    132: "lemma_mul_is_commutative",
    134: "lemma_mul_is_associative",
    136: "lemma_mul_is_associative",
    138: "lemma_mul_is_distributive",
    140: "lemma_mul_is_distributive",
    142: "lemma_mul_is_distributive",
    144: "lemma_mul_is_distributive",
    146: "lemma_mul_is_distributive",
    148: "lemma_mul_is_distributive",
    150: "lemma_mul_is_distributive",
    152: "lemma_mul_is_distributive",
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
            if self.name == "Mul":
                assert len(self.arguments) == 2
                return f"({self.arguments[0].to_verus_expr()} * {self.arguments[1].to_verus_expr()})"

            elif self.name == "Add":
                assert len(self.arguments) == 2
                return f"({self.arguments[0].to_verus_expr()} + {self.arguments[1].to_verus_expr()})"
            
            elif self.name == "Sub":
                assert len(self.arguments) == 2
                return f"({self.arguments[0].to_verus_expr()} - {self.arguments[1].to_verus_expr()})"
            
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
        (10010383067674129532, 14),
        (10025614845282315747, 19),
        (10150394785182611152, 22),
        (10158473915313311221, 17),
        (1019351439507244526, 25),
        (10310752968603430965, 26),
        (10347411120038867046, 18),
        (10397734997551711464, 18),
        (10605254345006356465, 24),
        (10659375977077386972, 27),
        (10812803665496885203, 18),
        (10897592030914879309, 17),
        (10996767105058152486, 20),
        (11093989237426846937, 17),
        (11136798364830944260, 20),
        (11150809716283307823, 22),
        (11169647372304905020, 15),
        (11271200891406283735, 8),
        (1131246867973038300, 25),
        (11321342827662598315, 19),
        (11468037660496618007, 28),
        (11509400854587548495, 15),
        (11546628732057865797, 11),
        (11559579205959100000, 28),
        (11825147686390842130, 11),
        (11968667455991221118, 23),
        (11991955548935593597, 26),
        (12088963696273517596, 26),
        (12091294745012006478, 24),
        (12167189731977238612, 20),
        (12272322958713611085, 17),
        (12454663024317473319, 17),
        (12462582095944317189, 23),
        (12514132642591022410, 25),
        (12550485510917026464, 8),
        (12641807374693005551, 23),
        (12676445640037346034, 22),
        (12779935399677393819, 14),
        (12788800289914997896, 19),
        (1284790712069252310, 20),
        (13106369083198756670, 24),
        (13348694943851565950, 4),
        (13402605405788420286, 27),
        (13440759468141265667, 19),
        (13452356439655812593, 3),
        (13524652801067133566, 21),
        (13530297155604201181, 23),
        (13876665199597111689, 21),
        (13990150058155071815, 13),
        (14040977382153817238, 5),
        (1407247653605915806, 23),
        (14090101086157970305, 18),
        (14120795730861728955, 20),
        (14407918698460325713, 18),
        (14460462004790160974, 19),
        (14542286719127506150, 18),
        (14575168783172289696, 15),
        (14654510788513669907, 8),
        (14744411643324346758, 12),
        (14764162346206151094, 8),
        (14998514565155564974, 24),
        (15023403850817364087, 19),
        (15041208865572613407, 17),
        (15197645479909712552, 17),
        (15213723651949408263, 27),
        (1526485803100522627, 21),
        (15294475969189781596, 5),
        (15296810156270931264, 19),
        (15312229723017405710, 17),
        (15323613370905244880, 12),
        (15394911057285899457, 17),
        (15549701504494115619, 25),
        (15729071383696623798, 21),
        (15759989188846083194, 26),
        (15770742889810683241, 28),
        (15852488998799190415, 19),
        (15878960253708145026, 23),
        (15904756395281607496, 22),
        (15956083435776837484, 9),
        (15977866127796107871, 13),
        (1600471499373671216, 26),
        (16040906275976474278, 21),
        (16126922845566555854, 1),
        (16221891383611739967, 16),
        (16279850040026406244, 20),
        (1636400704764515315, 18),
        (16383451365992985660, 10),
        (164236219866697108, 20),
        (16464657419560141308, 23),
        (16467394671022003734, 6),
        (16614881582051595759, 19),
        (16627886866770890955, 14),
        (16629974354197705848, 25),
        (16661510912686951609, 18),
        (1667337654596510450, 18),
        (16727114196946070052, 25),
        (16745581497411726556, 8),
        (1675701205702059556, 22),
        (16934100255213239693, 20),
        (17001117928371739642, 21),
        (17027965391815731210, 27),
        (17037612864152200606, 17),
        (17049639938228004113, 15),
        (17125596767219410934, 23),
        (17276940350966072881, 27),
        (17298556895922633107, 20),
        (17302800062061785357, 23),
        (17330110508073353049, 25),
        (17350080869350297916, 22),
        (1763281984466661887, 17),
        (17654380543801727730, 10),
        (17688099224096666937, 15),
        (17942325817951059502, 14),
        (17951261189751624492, 16),
        (17978765405434460539, 22),
        (17993913645443750663, 6),
        (18041382925430782131, 20),
        (18057393037062890410, 12),
        (18154595700487381511, 21),
        (18328614174984404072, 2),
        (18369409694645562088, 11),
        (18374056510323490960, 23),
        (186992415320269008, 18),
        (1870428492480195433, 8),
        (1903720889099580400, 20),
        (1919356812822784259, 12),
        (1984633738276779579, 26),
        (2027028218617745017, 22),
        (203918970033953925, 20),
        (2042314173136524624, 23),
        (2042723858303991207, 10),
        (2193788587161715333, 18),
        (2216803071140698363, 6),
        (2241149175590361516, 23),
        (2313700739316940897, 22),
        (2428745912322874132, 19),
        (2493523300483400241, 20),
        (2516786382402352663, 16),
        (2600419500924170598, 25),
        (2697211439849746383, 18),
        (2715611993323207999, 20),
        (2768453274278765674, 21),
        (2805539088094301822, 24),
        (2891839430639039113, 14),
        (2934117329353033998, 27),
        (2985690168187533016, 20),
        (3007502174683360204, 12),
        (3027989785754094706, 19),
        (3034872531678749337, 21),
        (3106586111090654302, 20),
        (3187215597013749221, 14),
        (3291020618319148333, 25),
        (3299406150661771757, 16),
        (3322844657195306459, 11),
        (3354312823931803703, 23),
        (359675259683091145, 26),
        (3598422476908079582, 19),
        (3724816130530305624, 23),
        (3773282015981746237, 15),
        (3783878411940359264, 22),
        (3791278692992896766, 12),
        (3813418385213240236, 20),
        (3892246039421652627, 19),
        (4136319418252927284, 14),
        (4290713111748107445, 22),
        (4326502880816456174, 5),
        (4380425621391362353, 25),
        (4428162985799193792, 13),
        (4488871651606761212, 22),
        (4490230228235018291, 23),
        (453978463885488113, 26),
        (4580998638562250768, 22),
        (4933622370344928084, 17),
        (4962501410352935923, 8),
        (5098774655042179034, 23),
        (5233015777625803401, 24),
        (5285968602769369298, 6),
        (5289912216819266849, 13),
        (5331428747546002168, 24),
        (5508863490063391896, 1),
        (5516837663209574677, 14),
        (5582820585840128871, 8),
        (568207880457963297, 19),
        (5691648938394929930, 11),
        (5751280887010390579, 15),
        (583441476344412455, 16),
        (586919262431847887, 15),
        (5924924948786400335, 11),
        (5944567491567735269, 18),
        (601463757446254393, 21),
        (6033808434929747191, 15),
        (6036400347252718449, 20),
        (6044325488623827733, 15),
        (6297514304111381047, 23),
        (6349881791523893674, 13),
        (6434697341965820735, 15),
        (6665166418180656779, 22),
        (6776590408354799954, 22),
        (6873950603460204398, 22),
        (6878346404358128900, 16),
        (6927092314837537010, 24),
        (7045881200950481896, 24),
        (7074193423473730439, 9),
        (7233768587032536787, 18),
        (7298262002629773612, 20),
        (7321824906820619456, 23),
        (7333014296418745115, 22),
        (7535043302391895578, 17),
        (7626132661144257466, 3),
        (7657017263690095665, 15),
        (7757966156712634293, 16),
        (781643039291689335, 19),
        (7855088246712589864, 15),
        (7876361007614496636, 17),
        (822122041320828559, 12),
        (8577837602559263134, 13),
        (8601151044767494818, 20),
        (8616598463962419202, 12),
        (8961033303928341538, 27),
        (9046713686224271634, 20),
        (9136951571367990167, 19),
        (926116782476474478, 12),
        (9405463958816067559, 25),
        (9505880585931356858, 26),
        (9514466543809959468, 12),
        (9602849478527771484, 5),
        (960450448923523377, 24),
        (9691159628085418774, 26),
        (9722941607487800285, 21),
        (9776236084697023252, 16),
        (9802516488547731685, 19),
        (9858311102561624313, 22),
        (9893459341669959620, 22),
        (9905135423731245277, 16),
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

        for assert_idx in range(num_asserts):
            print(f"### ({seed_idx + 1}/{len(seeds)}) seed {seed} assertion {assert_idx}")

            pa = EmitterParams(seed=seed, config_name="v_nl")
            er = ExperimentRunner(pa, overwrite=True)
            er.emit_verus_file(StepMode.FREE, actual_expr_num=assert_idx + 1, skip_expr_num=assert_idx)

            emitted_path = f"mariposa_data/v_nl/{seed}/nlqi_verus/src/main.rs"

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

                verus_term_strs = []
                for term in air_terms:
                    term_str = term.to_verus_expr()
                    if term_str.startswith("(") and term_str.endswith(")"):
                        term_str = term_str[1:-1]
                    verus_term_strs.append(term_str)

                manual_lemma = LINE_NUM_TO_MANUAL_LEMMA[quantifier_line_num]

                if used:
                    num_used_instantiations += 1
                    replace_assert_lines.append(f"\t\t{manual_lemma}({', '.join(verus_term_strs)});")
            
            replace_assert_lines.append("\t}")

            if num_used_instantiations != 0:
                assert_replace_map[assert_stmt_str] = "\n".join(replace_assert_lines)

        print(f"### generating instantiated source for seed {seed}")

        pa = EmitterParams(seed=seed, config_name="v_nl")
        er = ExperimentRunner(pa, overwrite=True)
        er.emit_verus_file(StepMode.FREE, actual_expr_num=num_asserts)

        emitted_path = f"mariposa_data/v_nl/{seed}/nlqi_verus/src/main.rs"

        with open(emitted_path) as f:
            source = f.read()
            source = re.sub(r"[\t ]*lemma_mul_properties_auto_1\(\);\n", "", source)
            for k, v in assert_replace_map.items():
                source = source.replace(k, v)

        with open(os.path.join(output_dir, f"instantiations-{seed}.rs"), "w") as f:
            f.write(source)

if __name__ == "__main__":
    main()
