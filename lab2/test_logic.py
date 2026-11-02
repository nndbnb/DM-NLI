import itertools
import unittest
from fractions import Fraction

from logic import (HALF, ONE, ZERO, FormulaSyntaxError, LogicError, analyze,
                   check_entailment, compare, evaluate, format_formula,
                   get_logic, parse_assignments, parse_formula, variables)
from variant1 import FORMULAS, RELATIONS, render_report


class ParserTests(unittest.TestCase):
    def test_all_connectives_and_precedence(self):
        self.assertEqual(parse_formula("¬p ∧ q ∨ r → s"),
                         parse_formula("((¬p ∧ q) ∨ r) → s"))

    def test_implication_is_left_associative(self):
        self.assertEqual(parse_formula("p→q→r"), parse_formula("(p→q)→r"))
        self.assertNotEqual(parse_formula("p→q→r"), parse_formula("p→(q→r)"))

    def test_aliases(self):
        self.assertEqual(parse_formula("!p && q || r -> s"), parse_formula("¬p∧q∨r→s"))
        for arrow in ["->", "=>", "⊃", "⇒", "→"]:
            self.assertEqual(parse_formula(f"p {arrow} q"), parse_formula("p→q"))

    def test_repeated_variables_and_identifiers(self):
        self.assertEqual(variables(parse_formula("p1∧p1∨q_2")), ("p1", "q_2"))

    def test_f_is_a_variable_in_lab2(self):
        self.assertEqual(evaluate(parse_formula("f"), {"f": ONE}, get_logic("C2")), ONE)

    def test_print_round_trip(self):
        for text in [*FORMULAS.values(), "¬¬p", "¬(p∨q)", "p→q→r", "(p)"]:
            with self.subTest(text=text):
                f = parse_formula(text)
                self.assertEqual(parse_formula(format_formula(f)), f)

    def test_invalid_syntax(self):
        for text in ["", "()", "p q", "p(q)", "p→", "∧p", "¬", "(p∨q", "p)", "p^^q", "p=q", "1"]:
            with self.subTest(text=text):
                with self.assertRaises(FormulaSyntaxError):
                    parse_formula(text)

    def test_resource_limits(self):
        for text in ["("*1000+"p"+")"*1000, "¬"*1000+"p", "→".join(["p"]*200), "p"*10001]:
            with self.subTest(length=len(text)):
                with self.assertRaises(LogicError):
                    parse_formula(text)


class OperationTests(unittest.TestCase):
    def test_negation_table(self):
        for code in ("K3", "L3"):
            self.assertEqual([get_logic(code).negate(x) for x in (ZERO, HALF, ONE)], [ONE, HALF, ZERO])

    def test_conjunction_table(self):
        expected = [[0, 0, 0], [0, HALF, HALF], [0, HALF, 1]]
        for code in ("K3", "L3"):
            self.assertEqual([[get_logic(code).conjunction(a, b) for b in (ZERO, HALF, ONE)]
                              for a in (ZERO, HALF, ONE)], expected)

    def test_disjunction_table(self):
        expected = [[0, HALF, 1], [HALF, HALF, 1], [1, 1, 1]]
        for code in ("K3", "L3"):
            self.assertEqual([[get_logic(code).disjunction(a, b) for b in (ZERO, HALF, ONE)]
                              for a in (ZERO, HALF, ONE)], expected)

    def test_kleene_implication_table(self):
        system = get_logic("K3")
        self.assertEqual([[system.implication(a, b) for b in system.domain] for a in system.domain],
                         [[1, 1, 1], [HALF, HALF, 1], [0, HALF, 1]])

    def test_lukasiewicz_implication_table(self):
        system = get_logic("L3")
        self.assertEqual([[system.implication(a, b) for b in system.domain] for a in system.domain],
                         [[1, 1, 1], [HALF, 1, 1], [0, HALF, 1]])

    def test_classical_implication_table(self):
        system = get_logic("C2")
        self.assertEqual([[system.implication(a, b) for b in system.domain] for a in system.domain],
                         [[1, 1], [0, 1]])

    def test_example_from_assignment(self):
        f = parse_formula("p→q")
        self.assertEqual(evaluate(f, {"p": HALF, "q": HALF}, get_logic("K3")), HALF)
        self.assertEqual(evaluate(f, {"p": HALF, "q": HALF}, get_logic("L3")), ONE)

    def test_boolean_restrictions_coincide(self):
        for a, b in itertools.product((ZERO, ONE), repeat=2):
            self.assertEqual(len({get_logic(code).implication(a, b) for code in ("C2", "K3", "L3")}), 1)


class AssignmentAndAnalysisTests(unittest.TestCase):
    def test_exact_value_parsing(self):
        self.assertEqual(parse_assignments(["p=0.5,q=1/2", "r=1"]), {"p": HALF, "q": HALF, "r": ONE})

    def test_invalid_assignments(self):
        for values in [["p"], ["p="], ["p=1/0"], ["p=hello"], ["p=0", "p=1"], ["=0"]]:
            with self.subTest(values=values):
                with self.assertRaises(LogicError):
                    parse_assignments(values)

    def test_missing_data(self):
        with self.assertRaisesRegex(LogicError, "не заданы q"):
            evaluate(parse_formula("p→q"), {"p": ONE}, get_logic("K3"))

    def test_extra_variable(self):
        with self.assertRaisesRegex(LogicError, "Лишние оценки"):
            evaluate(parse_formula("p"), {"p": ONE, "q": ZERO}, get_logic("L3"))

    def test_domain_is_checked(self):
        with self.assertRaises(LogicError):
            evaluate(parse_formula("p"), {"p": HALF}, get_logic("C2"))
        with self.assertRaises(LogicError):
            evaluate(parse_formula("p"), {"p": Fraction(1, 4)}, get_logic("L3"))

    def test_unknown_logic(self):
        with self.assertRaises(LogicError):
            get_logic("K4")

    def test_number_of_interpretations(self):
        f = parse_formula("p∧p∨q")
        self.assertEqual(len(analyze(f, get_logic("C2")).rows), 4)
        self.assertEqual(len(analyze(f, get_logic("K3")).rows), 9)

    def test_unsatisfiable_is_not_identically_false(self):
        f = parse_formula("p∧¬p")
        a = analyze(f, get_logic("K3"))
        self.assertFalse(a.satisfiable)
        self.assertFalse(a.identically_false)
        self.assertIsNone(a.witness)
        self.assertTrue(analyze(f, get_logic("C2")).identically_false)

    def test_validity_and_counterexamples(self):
        f = parse_formula("p→p")
        self.assertFalse(analyze(f, get_logic("K3")).valid)
        self.assertEqual(analyze(f, get_logic("K3")).counterexample.result, HALF)
        self.assertTrue(analyze(f, get_logic("L3")).valid)
        self.assertIsNone(analyze(f, get_logic("L3")).counterexample)

    def test_enumeration_limit(self):
        f = parse_formula("∨".join(f"p{i}" for i in range(11)))
        with self.assertRaisesRegex(LogicError, "177147 строк"):
            analyze(f, get_logic("K3"))


class EntailmentAndComparisonTests(unittest.TestCase):
    def test_modus_ponens_in_all_systems(self):
        for code in ("C2", "K3", "L3"):
            result = check_entailment([parse_formula("p"), parse_formula("p→q")], parse_formula("q"), get_logic(code))
            self.assertTrue(result.entails)
            self.assertFalse(result.vacuous)

    def test_missing_premise_has_counterexample(self):
        result = check_entailment([parse_formula("p→q")], parse_formula("q"), get_logic("C2"))
        self.assertFalse(result.entails)
        self.assertEqual(result.counterexample.values, (ZERO, ZERO))

    def test_half_conclusion_is_a_counterexample(self):
        result = check_entailment([], parse_formula("p→p"), get_logic("K3"))
        self.assertFalse(result.entails)
        self.assertEqual(result.counterexample.conclusion, HALF)

    def test_incompatible_premises(self):
        for code in ("C2", "K3", "L3"):
            result = check_entailment([parse_formula("p"), parse_formula("¬p")], parse_formula("q"), get_logic(code))
            self.assertTrue(result.entails)
            self.assertTrue(result.vacuous)
            self.assertEqual(result.model_count, 0)

    def test_empty_premises_mean_validity(self):
        for code in ("C2", "K3", "L3"):
            f = parse_formula("p∨¬p")
            self.assertEqual(check_entailment([], f, get_logic(code)).entails, analyze(f, get_logic(code)).valid)

    def test_variables_from_conclusion_are_included(self):
        a = check_entailment([parse_formula("p")], parse_formula("q"), get_logic("K3"))
        self.assertEqual(a.names, ("p", "q"))
        self.assertEqual(len(a.rows), 9)

    def test_half_premise_is_not_a_model(self):
        a = check_entailment([parse_formula("p∧¬p")], parse_formula("q"), get_logic("K3"))
        self.assertTrue(a.vacuous)

    def test_comparison_marks_invalid_classical_values(self):
        names, rows, analyses = compare(parse_formula("p→p"), [get_logic(c) for c in ("C2", "K3", "L3")])
        self.assertEqual(names, ("p",))
        self.assertEqual(rows[1], ((HALF,), (None, HALF, ONE)))
        self.assertEqual([a.valid for a in analyses], [True, False, True])

    def test_comparison_requires_distinct_systems(self):
        for codes in [("K3",), ("K3", "K3")]:
            with self.assertRaises(LogicError):
                compare(parse_formula("p"), [get_logic(c) for c in codes])


class VariantTests(unittest.TestCase):
    def test_formula_properties(self):
        expected = {"F1": [True, False, True], "F2": [True, False, False],
                    "F3": [False, False, False], "F4": [False, False, False], "F5": [True, False, False]}
        for label, text in FORMULAS.items():
            for i, code in enumerate(("C2", "K3", "L3")):
                with self.subTest(formula=label, logic=code):
                    a = analyze(parse_formula(text), get_logic(code))
                    self.assertEqual(a.valid, expected[label][i])
                    self.assertEqual(a.satisfiable, label != "F4")
                    self.assertEqual(a.identically_false, label == "F4" and code == "C2")

    def test_all_variant_rows_against_independent_integer_oracle(self):
        # Явные таблицы на кодах 0,1,2. Парсер и вычислитель программы не используются.
        tables = {"C2": [[2, 2, 2], [1, 1, 2], [0, 1, 2]],
                  "K3": [[2, 2, 2], [1, 1, 2], [0, 1, 2]],
                  "L3": [[2, 2, 2], [1, 2, 2], [0, 1, 2]]}
        for code in ("C2", "K3", "L3"):
            imp = lambda a, b: tables[code][a][b]
            def formulas(a):
                p, q, r = a.get("p"), a.get("q"), a.get("r")
                return [max(imp(p,q), imp(q,p)), imp(imp(imp(p,q),p),p),
                        max(min(p,2-p),q), min(min(p,2-p),q),
                        imp(min(imp(p,q),imp(q,r)),imp(p,r)) if r is not None else None]
            def relation(label, a):
                p,q,r,s,t = (a[n] for n in "pqrst")
                if label == "R1":
                    return [max(p,q),imp(p,r),imp(q,r),imp(r,s),imp(s,t)], t
                if label == "R2":
                    u = a["u"]
                    return [imp(p,q),imp(p,r),imp(min(q,r),s),imp(s,t),imp(t,u)], max(2-p,u)
                if label == "R3":
                    return [max(p,q),imp(p,r),imp(q,s),imp(r,t),imp(s,t)], min(t,max(p,2-p))
                u = a["u"]
                return [max(p,q),imp(p,r),imp(q,s),imp(max(r,s),t),imp(s,u)], imp(t,u)
            for index, text in enumerate(FORMULAS.values()):
                analysis = analyze(parse_formula(text), get_logic(code))
                for row in analysis.rows:
                    a = {n:int(v*2) for n,v in zip(analysis.names,row.values)}
                    self.assertEqual(row.result*2, formulas(a)[index])
            for label, (ps, conclusion) in RELATIONS.items():
                a = check_entailment(tuple(map(parse_formula, ps)),parse_formula(conclusion),get_logic(code))
                expected_models, expected_failure = 0, False
                for row in a.rows:
                    valuation = {n:int(v*2) for n,v in zip(a.names,row.values)}
                    values, result = relation(label, valuation)
                    self.assertEqual(tuple(v*2 for v in row.premises), tuple(values))
                    self.assertEqual(row.conclusion*2, result)
                    if all(v == 2 for v in values):
                        expected_models += 1
                        expected_failure |= result != 2
                self.assertEqual(a.model_count, expected_models)
                self.assertEqual(a.entails, not expected_failure)

    def test_relation_outcomes_and_model_counts(self):
        expected = {"R1": [(True,3),(True,5),(True,5)],
                    "R2": [(True,14),(True,41),(False,77)],
                    "R3": [(True,5),(False,9),(False,11)],
                    "R4": [(False,6),(False,11),(False,15)]}
        for label, (ps, c) in RELATIONS.items():
            for code, (holds, count) in zip(("C2","K3","L3"), expected[label]):
                with self.subTest(relation=label, logic=code):
                    a = check_entailment(tuple(map(parse_formula,ps)), parse_formula(c), get_logic(code))
                    self.assertEqual((a.entails, a.model_count), (holds,count))
                    if a.counterexample:
                        self.assertTrue(all(v == ONE for v in a.counterexample.premises))
                        self.assertNotEqual(a.counterexample.conclusion, ONE)

    def test_report_has_all_examples_and_full_tables(self):
        report = render_report()
        for name in [*FORMULAS, *RELATIONS]:
            self.assertIn("### " + name, report)
        self.assertIn("p=1/2, q=1/2, r=1/2, s=1/2, t=1/2, u=1/2", report)


if __name__ == "__main__":
    unittest.main(verbosity=2)
