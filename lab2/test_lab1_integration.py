"""Проверки реального переиспользования ЛР1, а не совпадения копий алгоритмов."""

from pathlib import Path
import ast
from fractions import Fraction
import os
import subprocess
import sys
import tempfile
import unittest
from unittest.mock import patch

import logic
from logic import foundation as lab1


class SharedFoundationTests(unittest.TestCase):
    def test_classes_and_parser_are_the_same_objects(self):
        for name in ["Variable", "FalseConst", "Implication", "Negation", "Conjunction",
                     "Disjunction", "Parser", "ProofVerifier", "match_axiom_schema"]:
            with self.subTest(name=name):
                self.assertIs(getattr(logic, name), getattr(lab1, name))
        self.assertIs(logic.FormulaSyntaxError, lab1.FormulaSyntaxError)
        self.assertIs(logic.FormulaLimitError, lab1.FormulaLimitError)
        self.assertIs(logic.LogicError, lab1.FormulaError)

    def test_no_local_ast_or_parser_copy(self):
        source = ast.parse(Path(logic.__file__).read_text(encoding="utf-8"))
        classes = {node.name for node in ast.walk(source) if isinstance(node, ast.ClassDef)}
        self.assertFalse(classes & {"Node", "Variable", "Implication", "Parser", "FalseConst"})

    def test_parsing_delegates_to_lab1(self):
        with patch.object(lab1, "parse_formula", wraps=lab1.parse_formula) as shared_parse:
            logic.parse_formula("!p & q")
            shared_parse.assert_called_once_with("!p & q", extended=True)

    def test_basic_ast_is_identical_between_labs(self):
        for text in ["p", "f", "p⊃q", "p⊃(q⊃p)", "((p⊃f)⊃f)⊃p"]:
            with self.subTest(text=text):
                self.assertEqual(lab1.parse_formula(text), logic.parse_formula(text))

    def test_original_lab1_language_remains_restricted(self):
        for text in ["¬p", "p∧q", "p∨q"]:
            with self.subTest(text=text):
                with self.assertRaises(lab1.FormulaSyntaxError):
                    lab1.parse_formula(text)
                self.assertIsNotNone(logic.parse_formula(text))
        ok, message = lab1.ProofVerifier().verify("p & q")
        self.assertFalse(ok)
        self.assertIn("не является ППФ", message)

    def test_extended_tree_contains_shared_nodes(self):
        formula = logic.parse_formula("!p & q | r -> f")
        self.assertIsInstance(formula, lab1.Implication)
        self.assertIs(formula.right, lab1.FALSE)
        self.assertIsInstance(formula.left, lab1.Disjunction)
        self.assertIsInstance(formula.left.left, lab1.Conjunction)
        self.assertIsInstance(formula.left.left.left, lab1.Negation)

    def test_false_constant_needs_no_assignment(self):
        self.assertIs(logic.parse_formula("f"), lab1.FALSE)
        for code in ("C2", "K3", "L3"):
            self.assertEqual(logic.evaluate(lab1.FALSE, {}, logic.get_logic(code)), 0)
            a = logic.analyze(lab1.FALSE, logic.get_logic(code))
            self.assertEqual(a.names, ())
            self.assertEqual(len(a.rows), 1)
            self.assertTrue(a.identically_false)
        with self.assertRaises(logic.LogicError):
            logic.evaluate(lab1.FALSE, {"f": Fraction(1)}, logic.get_logic("C2"))

    def test_lab1_axiom_is_evaluated_without_reparsing(self):
        for name, formula in lab1.ProofVerifier().axioms:
            with self.subTest(axiom=name):
                self.assertTrue(logic.analyze(formula, logic.get_logic("C2")).valid)
        self.assertEqual(logic.variables(lab1.ProofVerifier().axioms[2][1]), ("p",))

    def test_proved_tree_is_evaluated_without_conversion(self):
        verifier = lab1.ProofVerifier()
        self.assertTrue(verifier.verify("r⊃(s⊃r)")[0])
        formula = verifier.proof[0].formula
        self.assertEqual(logic.evaluate(formula, {"r": Fraction(1, 2), "s": Fraction(1)}, logic.get_logic("K3")), Fraction(1, 2))
        self.assertEqual(logic.evaluate(formula, {"r": Fraction(1, 2), "s": Fraction(1)}, logic.get_logic("L3")), 1)

    def test_schema_masks_accept_extended_subtrees(self):
        formula = logic.parse_formula("(a∧b)→(¬c→(a∧b))")
        verifier = lab1.ProofVerifier()
        self.assertEqual(verifier.find_axiom(formula), "A1")
        binding = lab1.match_axiom_schema(verifier.axioms[0][1], formula)
        self.assertIsInstance(binding["p"], lab1.Conjunction)
        self.assertIsInstance(binding["q"], lab1.Negation)
        self.assertIsNone(verifier.find_axiom(logic.parse_formula("(a∧b)→(¬c→(a∧d))")))

    def test_beta_traverses_extended_nodes(self):
        result = lab1.find_beta(logic.parse_formula("¬p→(q∨¬p)"), logic.parse_formula("¬r→(q∨¬r)"))
        self.assertEqual(result, ("p", lab1.Variable("r")))
        self.assertIsNone(lab1.find_beta(logic.parse_formula("¬p→(q∨¬p)"), logic.parse_formula("¬r→(q∨¬p)")))

    def test_schema_fixed_connective_is_not_a_mask(self):
        schema = logic.parse_formula("¬p→q")
        self.assertIsNotNone(lab1.match_axiom_schema(schema, logic.parse_formula("¬(a∧b)→c")))
        self.assertIsNone(lab1.match_axiom_schema(schema, logic.parse_formula("(a∧b)→c")))

    def test_common_printer_and_variable_collection(self):
        f = logic.parse_formula("¬(p∧f)∨q")
        self.assertEqual(lab1.variables_in(f), {"p", "q"})
        self.assertEqual(logic.variables(f), ("p", "q"))
        self.assertEqual(logic.format_formula(f), lab1.formula_to_string(f).replace("⊃", "→"))
        self.assertEqual(logic.parse_formula(logic.format_formula(f)), f)

    def test_limits_are_shared(self):
        self.assertEqual(logic.MAX_INPUT_LENGTH, lab1.MAX_INPUT_LENGTH)
        self.assertEqual(logic.MAX_DEPTH, lab1.MAX_FORMULA_DEPTH)
        with self.assertRaises(lab1.FormulaLimitError):
            logic.parse_formula("¬" * 101 + "p")
        self.assertIsNotNone(logic.parse_formula("(" * 100 + "p" + ")" * 100))

    def test_entrypoint_works_from_another_directory(self):
        script = Path(__file__).with_name("lab2_variant1.py").resolve()
        env = os.environ.copy()
        env["PYTHONIOENCODING"] = "utf-8"
        with tempfile.TemporaryDirectory() as directory:
            result = subprocess.run([sys.executable, str(script), "eval", "f", "--logic", "K3"],
                                    cwd=directory, capture_output=True, text=True, encoding="utf-8", env=env, timeout=10)
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertIn("f = 0", result.stdout)
