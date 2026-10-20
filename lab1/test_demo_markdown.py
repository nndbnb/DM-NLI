"""Запускает консольную программу по блокам input/expected из Markdown."""

from pathlib import Path
import os
import re
import subprocess
import sys
import unittest


ROOT = Path(__file__).resolve().parent
DOCUMENT = ROOT / "Сценарии_проверки_ЛР1.md"


def read_scenarios(path=DOCUMENT):
    text = path.read_text(encoding="utf-8")
    scenarios = []
    for section in re.split(r"(?m)^## ", text)[1:]:
        title = section.splitlines()[0]
        inputs = re.findall(r"(?ms)^```input\n(.*?)\n```", section)
        expected = re.findall(r"(?ms)^```expected\n(.*?)\n```", section)
        if not inputs and not expected:
            continue
        if len(inputs) != 1 or len(expected) != 1:
            raise ValueError(f"Неверные блоки сценария: {title}")
        scenarios.append((title, inputs[0], expected[0]))
    if not scenarios:
        raise ValueError("В Markdown нет сценариев")
    return scenarios


def run_scenario(program, inputs):
    env = os.environ.copy()
    env["PYTHONIOENCODING"] = "utf-8"
    result = subprocess.run(
        [sys.executable, str(program)],
        input=inputs + "\n", text=True, encoding="utf-8",
        capture_output=True, timeout=10, env=env,
    )
    if result.returncode or result.stderr:
        raise AssertionError(
            f"Код завершения {result.returncode}; stderr: {result.stderr}"
        )
    # Убираются только стартовая заставка и приглашения ввода.
    # Формулы, причины, номера строк и сообщения сравниваются целиком.
    if "formula> " not in result.stdout:
        raise AssertionError("Нет приглашения ввода")
    return result.stdout.split("formula> ", 1)[1].replace("formula> ", "").strip()


class DemoMarkdownTests(unittest.TestCase):
    def test_document_has_scenarios(self):
        self.assertGreaterEqual(len(read_scenarios()), 30)


def make_test(inputs, expected):
    def test(self):
        self.maxDiff = None
        actual = run_scenario(ROOT / "lab1_variant1.py", inputs)
        self.assertEqual(actual, expected.strip())
    return test


for number, (title, inputs, expected) in enumerate(read_scenarios(), 1):
    test = make_test(inputs, expected)
    test.__doc__ = title
    setattr(DemoMarkdownTests, f"test_scenario_{number:02}", test)


if __name__ == "__main__":
    unittest.main(verbosity=2)
