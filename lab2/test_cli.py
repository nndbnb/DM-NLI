from pathlib import Path
import os
import subprocess
import sys
import tempfile
import unittest


PROGRAM = Path(__file__).with_name("lab2_variant1.py")


def run(*args, stdin=None):
    env = os.environ.copy()
    env["PYTHONIOENCODING"] = "utf-8"
    return subprocess.run([sys.executable, str(PROGRAM), *args], input=stdin,
                          text=True, encoding="utf-8", capture_output=True, timeout=20, env=env)


class ConsoleTests(unittest.TestCase):
    def test_eval(self):
        for code, expected in [("K3","1/2"),("L3","1")]:
            result = run("eval","p->q","--logic",code,"--values","p=1/2","q=1/2")
            self.assertEqual(result.returncode,0,result.stderr)
            self.assertIn(f"p→q = {expected}",result.stdout)

    def test_missing_data(self):
        r = run("eval","p->q","--logic","K3","--values","p=1")
        self.assertEqual(r.returncode,2)
        self.assertIn("не заданы q",r.stderr)
        self.assertNotIn("Traceback",r.stderr)

    def test_classical_half_is_rejected(self):
        r = run("eval","p","--values","p=1/2")
        self.assertEqual(r.returncode,2)
        self.assertIn("недопустимо",r.stderr)

    def test_invalid_formula(self):
        r = run("table","p ->", "--logic","K3")
        self.assertEqual(r.returncode,2)
        self.assertNotIn("Traceback",r.stderr)

    def test_table_and_properties(self):
        r = run("table","p & !p","--logic","K3")
        self.assertEqual(r.returncode,0,r.stderr)
        self.assertIn("Формула невыполнима",r.stdout)
        self.assertNotIn("Формула тождественно ложна",r.stdout)

    def test_comparison(self):
        r = run("compare","p->p")
        self.assertEqual(r.returncode,0,r.stderr)
        self.assertIn("различий: 1",r.stdout)
        self.assertIn("Семантические свойства совпадают: нет",r.stdout)

    def test_comparison_of_given_interpretation(self):
        r = run("compare","p->q","--values","p=1/2","q=1/2")
        self.assertEqual(r.returncode,0,r.stderr)
        self.assertIn("C2: оценка недопустима",r.stdout)
        self.assertIn("K3: F=1/2.",r.stdout)
        self.assertIn("L3: F=1.",r.stdout)

    def test_true_entailment(self):
        r = run("entail","q","--premise","p","--premise","p->q","--logic","L3","--table")
        self.assertEqual(r.returncode,0,r.stderr)
        self.assertIn("Логическое следование: выполняется",r.stdout)
        self.assertIn("| p | q | A1 | A2 | B |",r.stdout)

    def test_false_entailment(self):
        r = run("entail","q","--premise","p->q","--logic","K3")
        self.assertEqual(r.returncode,0,r.stderr)
        self.assertIn("не выполняется",r.stdout)
        self.assertIn("Контрпример: p=0, q=0",r.stdout)

    def test_incompatible_premises_message(self):
        r = run("entail","q","--premise","p","--premise","!p","--logic","L3")
        self.assertEqual(r.returncode,0,r.stderr)
        self.assertIn("Посылки несовместимы",r.stdout)
        self.assertIn("формально",r.stdout)

    def test_interactive_menu_recovers_after_error(self):
        r = run(stdin="1\np->q\nK3\np=1\n1\np->q\nL3\np=1/2 q=1/2\n0\n")
        self.assertEqual(r.returncode,0,r.stderr)
        self.assertIn("не заданы q",r.stdout)
        self.assertIn("Значение формулы: 1.",r.stdout)

    def test_eof_exits_interactive_mode(self):
        r = run(stdin="")
        self.assertEqual(r.returncode,0,r.stderr)

    def test_report_can_be_written(self):
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / "report.md"
            r = run("report","--output",str(path))
            self.assertEqual(r.returncode,0,r.stderr)
            self.assertIn("### R4",path.read_text(encoding="utf-8"))

    def test_variant_command(self):
        r = run("variant")
        self.assertEqual(r.returncode,0,r.stderr)
        self.assertIn("F5:",r.stdout)
        self.assertIn("R4:",r.stdout)


if __name__ == "__main__":
    unittest.main(verbosity=2)
