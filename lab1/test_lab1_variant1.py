import unittest

from lab1_variant1 import (
    FormulaSyntaxError,
    ProofVerifier,
    find_beta,
    formula_to_string,
    parse_formula,
)


class ParserTests(unittest.TestCase):
    def test_axioms_are_valid(self):
        examples = [
            "p⊃(q⊃p)",
            "(s⊃(p⊃q))⊃((s⊃p)⊃(s⊃q))",
            "((p⊃f)⊃f)⊃p",
        ]
        for text in examples:
            with self.subTest(text=text):
                self.assertEqual(formula_to_string(parse_formula(text)), text)

    def test_ascii_arrow_is_supported(self):
        formula = parse_formula("p -> (q -> p)")
        self.assertEqual(formula_to_string(formula), "p⊃(q⊃p)")

    def test_chain_is_left_associative(self):
        self.assertEqual(parse_formula("p⊃q⊃r"), parse_formula("(p⊃q)⊃r"))
        self.assertNotEqual(parse_formula("p⊃q⊃r"), parse_formula("p⊃(q⊃r)"))

    def test_long_chain_is_left_associative(self):
        self.assertEqual(
            parse_formula("p⊃q⊃r⊃s"), parse_formula("((p⊃q)⊃r)⊃s")
        )

    def test_chains_inside_parentheses(self):
        self.assertEqual(
            parse_formula("p⊃(q⊃r⊃s)"), parse_formula("p⊃((q⊃r)⊃s)")
        )

    def test_redundant_parentheses(self):
        self.assertEqual(parse_formula("(((p⊃f))⊃f)⊃p"), parse_formula("((p⊃f)⊃f)⊃p"))
        self.assertEqual(parse_formula("((p))"), parse_formula("p"))

    def test_malformed_expressions_are_rejected(self):
        for text in ["", "()", "p⊃", "⊃p", "p⊃⊃q", "(p⊃q", "p⊃q)", "p q", "p(q)"]:
            with self.subTest(text=text):
                with self.assertRaises(FormulaSyntaxError):
                    parse_formula(text)

    def test_printed_formula_preserves_structure(self):
        for text in ["p⊃q⊃r", "p⊃(q⊃r)", "(p⊃q⊃r)⊃(s⊃f)"]:
            with self.subTest(text=text):
                formula = parse_formula(text)
                self.assertEqual(parse_formula(formula_to_string(formula)), formula)

    def test_invalid_symbol_is_rejected(self):
        with self.assertRaises(FormulaSyntaxError):
            parse_formula("p & q")


class BetaTests(unittest.TestCase):
    def test_single_complete_substitution(self):
        source = parse_formula("p⊃(q⊃p)")
        target = parse_formula("(r⊃s)⊃(q⊃(r⊃s))")
        result = find_beta(source, target)
        self.assertIsNotNone(result)
        variable, replacement = result
        self.assertEqual(variable, "p")
        self.assertEqual(formula_to_string(replacement), "r⊃s")

    def test_partial_substitution_is_rejected(self):
        source = parse_formula("p⊃(q⊃p)")
        target = parse_formula("r⊃(q⊃p)")
        self.assertIsNone(find_beta(source, target))

    def test_two_different_variables_cannot_change_at_once(self):
        source = parse_formula("p⊃(q⊃p)")
        target = parse_formula("r⊃(s⊃r)")
        self.assertIsNone(find_beta(source, target))

    def test_different_replacements_are_rejected(self):
        self.assertIsNone(find_beta(parse_formula("p⊃(q⊃p)"), parse_formula("r⊃(q⊃s)")))

    def test_false_constant_cannot_be_replaced(self):
        self.assertIsNone(find_beta(parse_formula("p⊃f"), parse_formula("p⊃q")))

    def test_variable_can_be_replaced_by_false(self):
        result = find_beta(parse_formula("p⊃(q⊃p)"), parse_formula("f⊃(q⊃f)"))
        self.assertEqual(result, ("p", parse_formula("f")))

    def test_replacement_can_contain_original_variable(self):
        result = find_beta(
            parse_formula("p⊃(q⊃p)"), parse_formula("(p⊃q)⊃(q⊃(p⊃q))")
        )
        self.assertEqual(result, ("p", parse_formula("p⊃q")))


class VerifierTests(unittest.TestCase):
    def test_axiom_beta_mp_chain(self):
        verifier = ProofVerifier()

        ok, _ = verifier.verify("p⊃(q⊃p)")
        self.assertTrue(ok)

        ok, msg = verifier.verify(
            "(p⊃(q⊃p))⊃(q⊃(p⊃(q⊃p)))"
        )
        self.assertTrue(ok)
        self.assertIn("β", msg)

        ok, msg = verifier.verify("q⊃(p⊃(q⊃p))")
        self.assertTrue(ok)
        self.assertIn("modus ponens", msg)

    def test_axiom_is_available_before_first_line(self):
        verifier = ProofVerifier()
        ok, msg = verifier.verify("r⊃(q⊃r)")
        self.assertTrue(ok)
        self.assertIn("β", msg)
        self.assertIn("аксиома A1", verifier.proof[0].reason)

    def test_mp_can_use_axiom_without_explicit_input(self):
        verifier = ProofVerifier()
        ok, _ = verifier.verify("(p⊃(q⊃p))⊃(q⊃(p⊃(q⊃p)))")
        self.assertTrue(ok)
        ok, msg = verifier.verify("q⊃(p⊃(q⊃p))")
        self.assertTrue(ok)
        self.assertIn("modus ponens", msg)
        self.assertIn("аксиома A1", verifier.proof[1].reason)
        self.assertEqual(len(verifier.proof), 2)

    def test_mp_requires_both_premises(self):
        verifier = ProofVerifier()
        # A3 имеет заключение p, но её антецедент не доказан.
        ok, _ = verifier.verify("p")
        self.assertFalse(ok)
        self.assertEqual(verifier.proof, [])

    def test_invalid_input_does_not_change_proof(self):
        verifier = ProofVerifier()
        verifier.verify("r⊃(q⊃r)")
        before = verifier.proof.copy()
        for text in ["p & q", "p", "p⊃"]:
            with self.subTest(text=text):
                ok, _ = verifier.verify(text)
                self.assertFalse(ok)
                self.assertEqual(verifier.proof, before)

    def test_duplicate_formula_is_not_added_twice(self):
        verifier = ProofVerifier()
        verifier.verify("r⊃(q⊃r)")
        ok, _ = verifier.verify("r -> (q -> r)")
        self.assertTrue(ok)
        self.assertEqual(len(verifier.proof), 1)

    def test_axioms_remain_available_after_clear(self):
        verifier = ProofVerifier()
        verifier.verify("r⊃(q⊃r)")
        verifier.clear()
        self.assertEqual(verifier.proof, [])
        ok, _ = verifier.verify("r⊃(q⊃r)")
        self.assertTrue(ok)
        self.assertEqual(verifier.proof[0].number, 1)

    def test_valid_but_not_derivable_formula_is_rejected(self):
        verifier = ProofVerifier()
        ok, msg = verifier.verify("p")
        self.assertFalse(ok)
        self.assertIn("является ППФ", msg)


if __name__ == "__main__":
    unittest.main(verbosity=2)
