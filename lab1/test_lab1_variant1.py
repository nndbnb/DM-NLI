import unittest
from itertools import product

from lab1_variant1 import (
    FormulaSyntaxError,
    FormulaLimitError,
    FalseConst,
    Variable,
    ProofVerifier,
    find_beta,
    formula_to_string,
    match_axiom_schema,
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


class AxiomSchemaTests(unittest.TestCase):
    A1 = parse_formula("p⊃(q⊃p)")
    A2 = parse_formula("(s⊃(p⊃q))⊃((s⊃p)⊃(s⊃q))")
    A3 = parse_formula("((p⊃f)⊃f)⊃p")

    def test_two_independent_variable_masks(self):
        result = match_axiom_schema(self.A1, parse_formula("r⊃(s⊃r)"))
        self.assertEqual(result, {"p": Variable("r"), "q": Variable("s")})

    def test_two_compound_subtrees(self):
        result = match_axiom_schema(self.A1, parse_formula("(r⊃s)⊃((t⊃f)⊃(r⊃s))"))
        self.assertEqual(result, {"p": parse_formula("r⊃s"), "q": parse_formula("t⊃f")})

    def test_same_tree_for_distinct_masks_is_allowed(self):
        result = match_axiom_schema(self.A1, parse_formula("x⊃(x⊃x)"))
        self.assertEqual(result, {"p": Variable("x"), "q": Variable("x")})

    def test_false_can_fill_a_variable_mask(self):
        self.assertIsNotNone(match_axiom_schema(self.A1, parse_formula("f⊃(f⊃f)")))
        self.assertIsNotNone(match_axiom_schema(self.A3, parse_formula("((f⊃f)⊃f)⊃f")))

    def test_swapping_names_is_not_recursive_substitution(self):
        result = match_axiom_schema(self.A1, parse_formula("q⊃(p⊃q)"))
        self.assertEqual(result, {"p": Variable("q"), "q": Variable("p")})

    def test_original_name_can_occur_inside_binding(self):
        result = match_axiom_schema(self.A1, parse_formula("(p⊃q)⊃(p⊃(p⊃q))"))
        self.assertEqual(result, {"p": parse_formula("p⊃q"), "q": Variable("p")})

    def test_repeated_mask_requires_equal_subtrees(self):
        for text in ["r⊃(s⊃t)", "(a⊃b)⊃(s⊃(a⊃c))", "r⊃(s⊃(r⊃r))"]:
            with self.subTest(text=text):
                self.assertIsNone(match_axiom_schema(self.A1, parse_formula(text)))

    def test_implication_nodes_are_fixed(self):
        for text in ["p", "f", "p⊃q", "(p⊃q)⊃p"]:
            with self.subTest(text=text):
                self.assertIsNone(match_axiom_schema(self.A1, parse_formula(text)))

    def test_a2_repeated_masks(self):
        text = "((a⊃b)⊃(c⊃d))⊃(((a⊃b)⊃c)⊃((a⊃b)⊃d))"
        self.assertEqual(match_axiom_schema(self.A2, parse_formula(text)),
                         {"s": parse_formula("a⊃b"), "p": Variable("c"), "q": Variable("d")})
        verifier = ProofVerifier()
        self.assertEqual(verifier.find_axiom(parse_formula(text)), "A2")

    def test_a2_inconsistent_s_p_and_q_are_rejected(self):
        for text in [
            "((a⊃b)⊃(c⊃d))⊃(((a⊃b)⊃c)⊃(e⊃d))",
            "((a⊃b)⊃(c⊃d))⊃(((a⊃b)⊃e)⊃((a⊃b)⊃d))",
            "((a⊃b)⊃(c⊃d))⊃(((a⊃b)⊃c)⊃((a⊃b)⊃e))",
        ]:
            with self.subTest(text=text):
                self.assertIsNone(match_axiom_schema(self.A2, parse_formula(text)))
                self.assertIsNone(ProofVerifier().find_axiom(parse_formula(text)))

    def test_a3_compound_mask(self):
        text = "(((a⊃b)⊃f)⊃f)⊃(a⊃b)"
        self.assertEqual(match_axiom_schema(self.A3, parse_formula(text)), {"p": parse_formula("a⊃b")})
        self.assertEqual(ProofVerifier().find_axiom(parse_formula(text)), "A3")

    def test_false_in_a3_is_not_a_mask(self):
        for text in ["((p⊃x)⊃x)⊃p", "((p⊃f)⊃x)⊃p", "((p⊃x)⊃f)⊃p"]:
            with self.subTest(text=text):
                self.assertIsNone(match_axiom_schema(self.A3, parse_formula(text)))

    def test_empty_binding_map_is_still_a_success(self):
        self.assertEqual(match_axiom_schema(parse_formula("f"), parse_formula("f")), {})
        self.assertIsNone(match_axiom_schema(parse_formula("f"), parse_formula("p")))

    def test_bindings_do_not_leak_between_calls_or_schemas(self):
        self.assertIsNone(match_axiom_schema(self.A1, parse_formula("x⊃(y⊃z)")))
        self.assertIsNotNone(match_axiom_schema(self.A1, parse_formula("r⊃(s⊃r)")))
        self.assertEqual(ProofVerifier().find_axiom(parse_formula("((r⊃f)⊃f)⊃r")), "A3")

    def test_generated_instances_and_their_semantics(self):
        # Независимое построение экземпляров по структурным операциям.
        # Для каждого из 155 экземпляров проверяется истинность на всех оценках.
        atoms = ["a", "b", "f", "(a⊃b)", "(b⊃a)"]
        examples = []
        for a, b in product(atoms, repeat=2):
            examples.append(("A1", f"{a}⊃({b}⊃{a})"))
        for s, p, q in product(atoms, repeat=3):
            examples.append(("A2", f"({s}⊃({p}⊃{q}))⊃(({s}⊃{p})⊃({s}⊃{q}))"))
        for a in atoms:
            examples.append(("A3", f"(({a}⊃f)⊃f)⊃{a}"))
        self.assertEqual(len(examples), 155)

        def evaluate(node, values):
            if isinstance(node, Variable):
                return values[node.name]
            if isinstance(node, FalseConst):
                return False
            return not evaluate(node.left, values) or evaluate(node.right, values)

        for name, text in examples:
            with self.subTest(schema=name, formula=text):
                formula = parse_formula(text)
                schema = dict(ProofVerifier().axioms)[name]
                self.assertIsNotNone(match_axiom_schema(schema, formula))
                self.assertTrue(ProofVerifier().verify(text)[0])
                for a, b in product([False, True], repeat=2):
                    self.assertTrue(evaluate(formula, {"a": a, "b": b}))


class VerifierTests(unittest.TestCase):
    def test_axiom_schema_mp_chain(self):
        verifier = ProofVerifier()

        ok, _ = verifier.verify("p⊃(q⊃p)")
        self.assertTrue(ok)

        ok, msg = verifier.verify(
            "(p⊃(q⊃p))⊃(q⊃(p⊃(q⊃p)))"
        )
        self.assertTrue(ok)
        self.assertIn("схемы аксиомы A1", msg)
        self.assertNotIn("по правилу β", msg)

        ok, msg = verifier.verify("q⊃(p⊃(q⊃p))")
        self.assertTrue(ok)
        self.assertIn("modus ponens", msg)

    def test_axiom_is_available_before_first_line(self):
        verifier = ProofVerifier()
        ok, msg = verifier.verify("r⊃(s⊃r)")
        self.assertTrue(ok)
        self.assertIn("схемы аксиомы A1", msg)
        self.assertEqual(verifier.proof[0].reason, "аксиома A1")

    def test_beta_still_applies_to_non_axiom_theorems(self):
        verifier = ProofVerifier()
        for text in [
            "s⊃((s⊃s)⊃s)",
            "(s⊃((s⊃s)⊃s))⊃((s⊃(s⊃s))⊃(s⊃s))",
            "(s⊃(s⊃s))⊃(s⊃s)",
            "s⊃(s⊃s)",
            "s⊃s",
        ]:
            self.assertTrue(verifier.verify(text)[0], text)
        ok, message = verifier.verify("r⊃r")
        self.assertTrue(ok)
        self.assertIn("по правилу β", message)
        self.assertIsNone(verifier.find_axiom(parse_formula("r⊃r")))

    def test_beta_of_non_axiom_remains_atomic(self):
        verifier = ProofVerifier()
        for text in [
            "p⊃((p⊃p)⊃p)",
            "(p⊃((p⊃p)⊃p))⊃((p⊃(p⊃p))⊃(p⊃p))",
            "(p⊃(p⊃p))⊃(p⊃p)",
            "p⊃(p⊃p)",
            "p⊃p",
            "q⊃(p⊃p)",
        ]:
            self.assertTrue(verifier.verify(text)[0], text)
        target = "s⊃(r⊃r)"
        self.assertFalse(verifier.verify(target)[0])
        self.assertIn("по правилу β", verifier.verify("q⊃(r⊃r)")[1])
        self.assertIn("по правилу β", verifier.verify(target)[1])

    def test_invalid_schema_instance_does_not_change_history(self):
        verifier = ProofVerifier()
        self.assertTrue(verifier.verify("r⊃(s⊃r)")[0])
        previous = verifier.proof.copy()
        self.assertFalse(verifier.verify("r⊃(s⊃t)")[0])
        self.assertEqual(verifier.proof, previous)

    def test_mp_can_use_axiom_without_explicit_input(self):
        verifier = ProofVerifier()
        ok, _ = verifier.verify("(p⊃(q⊃p))⊃(q⊃(p⊃(q⊃p)))")
        self.assertTrue(ok)
        ok, msg = verifier.verify("q⊃(p⊃(q⊃p))")
        self.assertTrue(ok)
        self.assertIn("modus ponens", msg)
        self.assertIn("аксиомы A1", verifier.proof[1].reason)
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


class DiagnosticAndLimitTests(unittest.TestCase):
    def test_missing_mp_antecedent_is_named(self):
        verifier = ProofVerifier()
        ok, message = verifier.verify("q⊃p")
        self.assertFalse(ok)
        self.assertIn("не хватает посылки p.", message)
        self.assertEqual(verifier.proof, [])

    def test_missing_mp_implication_is_reported(self):
        ok, message = ProofVerifier().verify("s⊃s")
        self.assertFalse(ok)
        self.assertIn("не найдены обе посылки A⊃B и A с заключением s⊃s.", message)

    def test_nesting_limit_boundary_is_valid(self):
        self.assertEqual(parse_formula("(" * 100 + "p" + ")" * 100), parse_formula("p"))

    def test_tree_depth_boundary_is_valid(self):
        self.assertIsNotNone(parse_formula("⊃".join(["p"] * 101)))

    def test_extreme_nesting_is_controlled(self):
        verifier = ProofVerifier()
        ok, message = verifier.verify("(" * 600 + "p" + ")" * 600)
        self.assertFalse(ok)
        self.assertIn("Формула не проверена:", message)
        self.assertNotIn("не является ППФ", message)
        self.assertEqual(verifier.proof, [])
        self.assertTrue(verifier.verify("r⊃(q⊃r)")[0])

    def test_long_unparenthesized_chain_is_controlled(self):
        with self.assertRaises(FormulaLimitError):
            parse_formula("⊃".join(["p"] * 1000))

    def test_input_length_limit_is_controlled(self):
        with self.assertRaises(FormulaLimitError):
            parse_formula("p" * 20001)
        # Ровно 20000 символов допустимы как один идентификатор.
        self.assertEqual(parse_formula("p" * 20000), Variable("p" * 20000))

    def test_limit_does_not_change_existing_history(self):
        verifier = ProofVerifier()
        verifier.verify("r⊃(q⊃r)")
        before = verifier.proof.copy()
        self.assertFalse(verifier.verify("p" * 20001)[0])
        self.assertEqual(verifier.proof, before)


class SemanticTests(unittest.TestCase):
    def test_accepted_small_formulas_are_tautologies(self):
        # Независимая семантическая проверка правильности принятых формул.
        # Не требует принятия всех тавтологий: это верификатор одного шага.
        def evaluate(formula, values):
            if isinstance(formula, Variable):
                return values[formula.name]
            if isinstance(formula, FalseConst):
                return False
            return not evaluate(formula.left, values) or evaluate(formula.right, values)

        atoms = ["p", "q", "f"]
        level_one = atoms + [f"({a}⊃{b})" for a in atoms for b in atoms]
        formulas = set(atoms + [f"({a}⊃{b})" for a in level_one for b in level_one])
        self.assertEqual(len(formulas), 147)
        verifier = ProofVerifier()
        for text in sorted(formulas):
            with self.subTest(formula=text):
                ok, _ = verifier.verify(text)
                if ok:
                    formula = parse_formula(text)
                    for p, q in product([False, True], repeat=2):
                        self.assertTrue(evaluate(formula, {"p": p, "q": q}))


if __name__ == "__main__":
    unittest.main(verbosity=2)
