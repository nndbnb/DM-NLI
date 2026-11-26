"""Регрессии случая с фотографии и MP с не введёнными экземплярами схем."""

from itertools import product
import unittest

from lab1_variant1 import (
    FALSE, FalseConst, FormulaLimitError, Implication, ProofVerifier, Variable,
    find_beta, formula_to_string, instantiate_axiom_schema, match_axiom_schema,
    parse_formula,
)


class SchemaModusPonensTests(unittest.TestCase):
    def assert_mp_witness(self, verifier, text):
        target = parse_formula(text)
        result = verifier.find_mp(target)
        self.assertIsNotNone(result, text)
        major, minor = result
        self.assertEqual(major.formula.right, target)
        self.assertEqual(major.formula.left, minor.formula)
        available = {s.formula for s in verifier.all_sources()}
        for source in result:
            self.assertTrue(source.formula in available or
                            verifier.find_axiom(source.formula) is not None)

    def test_screenshot_theorem_in_an_empty_session(self):
        verifier = ProofVerifier()
        text = "f⊃f⊃(r->(s->r))"
        self.assert_mp_witness(verifier, text)
        ok, message = verifier.verify(text)
        self.assertTrue(ok)
        self.assertIn("modus ponens", message)
        self.assertEqual(len(verifier.proof), 1)
        self.assertEqual(verifier.proof[0].reason,
                         "modus ponens из экземпляра схемы аксиомы A1 и экземпляра схемы аксиомы A1")

    def test_screenshot_sequence_and_repeat(self):
        verifier = ProofVerifier()
        for text in ["((p⊃f)⊃f)⊃p",
                     "r->(s->r)⊃f⊃f⊃(r->(s->r))",
                     "f⊃f⊃(r->(s->r))"]:
            self.assertTrue(verifier.verify(text)[0], text)
        ok, message = verifier.verify("(f->f)->(r->(s->r))")
        self.assertTrue(ok)
        self.assertIn("строка 3", message)
        self.assertEqual(len(verifier.proof), 3)

    def test_non_tautological_screenshot_variant_is_not_proved_by_a3(self):
        verifier = ProofVerifier()
        self.assertTrue(verifier.verify("r->(s->p)⊃f⊃f⊃(r->(s->p))")[0])
        previous = verifier.proof.copy()
        ok, message = verifier.verify("f⊃f⊃(r->(s->p))")
        self.assertFalse(ok)
        self.assertIn("является ППФ (синтаксис корректен)", message)
        self.assertIn("Шаг не принят", message)
        self.assertNotIn("не является ППФ", message)
        self.assertEqual(verifier.proof, previous)

    def test_concrete_major_can_use_an_implicit_minor_axiom(self):
        verifier = ProofVerifier()
        major = "(r⊃(s⊃r))⊃(t⊃(r⊃(s⊃r)))"
        self.assertTrue(verifier.verify(major)[0])
        self.assert_mp_witness(verifier, "t⊃(r⊃(s⊃r))")
        self.assertTrue(verifier.verify("t⊃(r⊃(s⊃r))")[0])
        self.assertEqual(verifier.proof[-1].reason,
                         "modus ponens из строки 1 и экземпляра схемы аксиомы A1")

    def test_implicit_major_can_use_a_previous_non_axiom(self):
        verifier = ProofVerifier()
        for text in ["p⊃((p⊃p)⊃p)",
                     "(p⊃((p⊃p)⊃p))⊃((p⊃(p⊃p))⊃(p⊃p))",
                     "(p⊃(p⊃p))⊃(p⊃p)", "p⊃(p⊃p)", "p⊃p"]:
            self.assertTrue(verifier.verify(text)[0], text)
        self.assert_mp_witness(verifier, "q⊃(p⊃p)")
        self.assertTrue(verifier.verify("q⊃(p⊃p)")[0])
        self.assertIn("и строки 5", verifier.proof[-1].reason)

    def test_a2_can_supply_an_implicit_major(self):
        verifier = ProofVerifier()
        text = "(s⊃p)⊃(s⊃s)"
        self.assertIsNone(verifier.find_axiom(parse_formula(text)))
        self.assert_mp_witness(verifier, text)
        self.assertTrue(verifier.verify(text)[0])
        self.assertEqual(verifier.proof[-1].reason,
                         "modus ponens из экземпляра схемы аксиомы A2 и экземпляра схемы аксиомы A1")

    def test_a3_can_supply_an_implicit_major(self):
        verifier = ProofVerifier()
        self.assert_mp_witness(verifier, "f⊃f")
        self.assertTrue(verifier.verify("f⊃f")[0])
        self.assertEqual(verifier.proof[-1].reason,
                         "modus ponens из экземпляра схемы аксиомы A3 и экземпляра схемы аксиомы A3")

    def test_all_axiom_families_can_supply_a_compound_minor(self):
        atoms = ["r", "f", "(r⊃s)"]
        minors = []
        for a, b in product(atoms, repeat=2):
            minors.append(f"{a}⊃({b}⊃{a})")
        for s, p, q in product(atoms, repeat=3):
            minors.append(f"({s}⊃({p}⊃{q}))⊃(({s}⊃{p})⊃({s}⊃{q}))")
        for a in atoms:
            minors.append(f"(({a}⊃f)⊃f)⊃{a}")
        self.assertEqual(len(minors), 39)
        for minor, condition in product(minors, atoms):
            text = f"{condition}⊃({minor})"
            with self.subTest(formula=text):
                verifier = ProofVerifier()
                self.assert_mp_witness(verifier, text)
                self.assertTrue(verifier.verify(text)[0])

    def test_a2_masks_can_be_compound(self):
        for s, p in product(["r", "f", "(r⊃s)"], repeat=2):
            text = f"({s}⊃{p})⊃({s}⊃{s})"
            with self.subTest(formula=text):
                verifier = ProofVerifier()
                self.assert_mp_witness(verifier, text)
                self.assertTrue(verifier.verify(text)[0])

    def test_mixed_arrow_aliases_preserve_the_screenshot_formula(self):
        for a, b, c, d in product(["⊃", "->", "=>", "→", "⇒"], repeat=4):
            text = f"f{a}f{b}(r{c}(s{d}r))"
            with self.subTest(formula=text):
                self.assertTrue(ProofVerifier().verify(text)[0])
                self.assertEqual(parse_formula(text), parse_formula("(f⊃f)⊃(r⊃(s⊃r))"))

    def test_no_arbitrary_antecedent_or_self_support_is_assumed(self):
        for text in ["p", "f", "p⊃q", "p⊃p", "f⊃f⊃(r⊃(s⊃p))"]:
            with self.subTest(formula=text):
                verifier = ProofVerifier()
                self.assertFalse(verifier.verify(text)[0])
                self.assertEqual(verifier.proof, [])

    def test_clear_removes_lemmas_but_preserves_implicit_axioms(self):
        verifier = ProofVerifier()
        self.assertTrue(verifier.verify("(f⊃f)⊃(r⊃(s⊃r))")[0])
        verifier.clear()
        self.assertEqual(verifier.proof, [])
        self.assertTrue(verifier.verify("(f⊃f)⊃(r⊃(s⊃r))")[0])
        self.assertEqual(verifier.proof[0].number, 1)

    def test_instantiation_does_not_reenter_bound_trees(self):
        schema = parse_formula("p⊃(q⊃p)")
        bindings = {"p": parse_formula("p⊃q"), "q": Variable("p")}
        result = instantiate_axiom_schema(schema, bindings)
        self.assertEqual(result, parse_formula("(p⊃q)⊃(p⊃(p⊃q))"))
        self.assertEqual(bindings["p"], parse_formula("p⊃q"))

    def test_instantiation_preserves_false_and_requires_every_mask(self):
        schema = parse_formula("((p⊃f)⊃f)⊃p")
        self.assertEqual(instantiate_axiom_schema(schema, {"p": Variable("q"), "f": Variable("x")}),
                         parse_formula("((q⊃f)⊃f)⊃q"))
        self.assertIsNone(instantiate_axiom_schema(schema, {}))

    def test_syntax_failure_and_unjustified_step_are_distinct(self):
        verifier = ProofVerifier()
        for text in ["()", "p⊃", "(p⊃q", "p & q"]:
            ok, message = verifier.verify(text)
            self.assertFalse(ok)
            self.assertIn("не является ППФ", message)
            self.assertNotIn("Шаг не принят", message)
        ok, message = verifier.verify("r⊃(s⊃p)")
        self.assertFalse(ok)
        self.assertIn("синтаксис корректен", message)
        self.assertIn("Шаг не принят", message)
        self.assertNotIn("не является ППФ", message)

    def test_mp_does_not_relax_beta_uniformity(self):
        self.assertIsNone(find_beta(parse_formula("p⊃(q⊃p)"), parse_formula("r⊃(s⊃r)")))
        # Эта формула всё равно принимается по A1, а не запрещённой β.
        self.assertIn("схемы аксиомы A1", ProofVerifier().verify("r⊃(s⊃r)")[1])

    def test_unbound_masks_in_non_variant_schemas_are_not_invented(self):
        verifier = ProofVerifier()
        verifier.axioms = [("custom", parse_formula("x⊃(y⊃z)"))]
        # Консеквент связывает y,z, но не x: подставлять имя x нельзя.
        self.assertIsNone(verifier.find_mp(parse_formula("p⊃q")))


class GeneratedFormulaTests(unittest.TestCase):
    def test_all_small_trees_parse_round_trip_and_accepted_ones_are_sound(self):
        atoms = [Variable("p"), Variable("q"), FALSE]
        levels = [atoms]
        for size in range(1, 5):
            levels.append([Implication(left, right)
                           for left_size in range(size)
                           for left in levels[left_size]
                           for right in levels[size - 1 - left_size]])
        trees = [tree for level in levels for tree in level]
        self.assertEqual(len(trees), 3873)

        def independent_text(node, arrow):
            if isinstance(node, Variable):
                return node.name
            if isinstance(node, FalseConst):
                return "f"
            return f"({independent_text(node.left, arrow)}{arrow}{independent_text(node.right, arrow)})"

        def classical(node, values):
            if isinstance(node, Variable):
                return values[node.name]
            if isinstance(node, FalseConst):
                return False
            return not classical(node.left, values) or classical(node.right, values)

        for tree in trees:
            with self.subTest(formula=independent_text(tree, "⊃")):
                for arrow in ["⊃", "->", "=>", "→", "⇒"]:
                    self.assertEqual(parse_formula(independent_text(tree, arrow)), tree)
                self.assertEqual(parse_formula(formula_to_string(tree)), tree)
                verifier = ProofVerifier()
                accepted, message = verifier.verify(independent_text(tree, "⊃"))
                self.assertNotIn("не является ППФ", message)
                if accepted:
                    for p, q in product([False, True], repeat=2):
                        self.assertTrue(classical(tree, {"p": p, "q": q}))
                    if verifier.proof[0].reason.startswith("modus ponens"):
                        major, minor = verifier.find_mp(tree)
                        self.assertEqual(major.formula.left, minor.formula)
                        self.assertEqual(major.formula.right, tree)


if __name__ == "__main__":
    unittest.main(verbosity=2)
