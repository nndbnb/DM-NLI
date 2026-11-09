"""Семантическое расширение ЛР1. AST, парсер и схемы импортируются из lab1."""

from dataclasses import dataclass
from fractions import Fraction
from itertools import product
from pathlib import Path
import re
import sys
from typing import Mapping


# Поддерживается запуск python lab2/lab2_variant1.py из любого каталога.
# Здесь подключается исходный модуль ЛР1, копии его кода в ЛР2 нет.
LAB1_DIRECTORY = Path(__file__).resolve().parents[1] / "lab1"
if str(LAB1_DIRECTORY) not in sys.path:
    sys.path.insert(0, str(LAB1_DIRECTORY))

import lab1_variant1 as foundation
from lab1_variant1 import (
    Variable, FalseConst, Implication, Negation, Conjunction, Disjunction,
    Formula as Node, FormulaError as LogicError, FormulaSyntaxError,
    FormulaLimitError, Parser, ProofVerifier, match_axiom_schema,
    MAX_INPUT_LENGTH, MAX_FORMULA_DEPTH, variables_in,
)

ZERO, HALF, ONE = Fraction(0), Fraction(1, 2), Fraction(1)
MAX_DEPTH = MAX_FORMULA_DEPTH
MAX_ROWS = 100000


def parse_formula(text: str) -> Node:
    return foundation.parse_formula(text, extended=True)


def variables(formula: Node) -> tuple[str, ...]:
    return tuple(sorted(variables_in(formula)))


def format_formula(formula: Node, nested=False) -> str:
    return foundation.formula_to_string(formula, nested).replace("⊃", "→")


def format_value(value: Fraction) -> str:
    return str(value)


@dataclass(frozen=True)
class LogicSystem:
    code: str
    title: str
    domain: tuple[Fraction, ...]

    def negate(self, a):
        return ONE - a

    def conjunction(self, a, b):
        return min(a, b)

    def disjunction(self, a, b):
        return max(a, b)

    def implication(self, a, b):
        if self.code == "L3":
            return min(ONE, ONE - a + b)
        return max(ONE - a, b)


SYSTEMS = {
    "C2": LogicSystem("C2", "Классическая двузначная логика", (ZERO, ONE)),
    "K3": LogicSystem("K3", "Сильная трёхзначная логика Клини", (ZERO, HALF, ONE)),
    "L3": LogicSystem("L3", "Трёхзначная логика Лукасевича", (ZERO, HALF, ONE)),
}


def get_logic(code: str) -> LogicSystem:
    try:
        return SYSTEMS[code.upper()]
    except KeyError:
        raise LogicError(f"Неизвестная логика {code!r}. Допустимы C2, K3, L3.") from None


def parse_assignments(items) -> dict[str, Fraction]:
    result = {}
    for item in items:
        for entry in item.split(","):
            if entry.count("=") != 1:
                raise LogicError(f"Оценка должна иметь вид p=1/2: {entry!r}.")
            name, text = (part.strip() for part in entry.split("="))
            if not re.fullmatch(r"[A-Za-z][A-Za-z0-9_]*", name):
                raise LogicError(f"Неверное имя переменной {name!r}.")
            if name in result:
                raise LogicError(f"Повторная оценка переменной {name}.")
            try:
                result[name] = Fraction(text)
            except (ValueError, ZeroDivisionError):
                raise LogicError(f"Неверное значение {text!r} для {name}.") from None
    return result


def validate_assignment(formula, assignment, system):
    required = set(variables(formula))
    missing = required - assignment.keys()
    if missing:
        raise LogicError("Недостаточно данных: не заданы " + ", ".join(sorted(missing)) + ".")
    extra = assignment.keys() - required
    if extra:
        raise LogicError("Лишние оценки: " + ", ".join(sorted(extra)) + ".")
    for name, value in assignment.items():
        if value not in system.domain:
            raise LogicError(f"Значение {value} для {name} недопустимо в {system.code}.")


def _evaluate(formula: Node, assignment: Mapping[str, Fraction], system: LogicSystem):
    if isinstance(formula, Variable):
        return assignment[formula.name]
    if isinstance(formula, FalseConst):
        return ZERO
    if isinstance(formula, Negation):
        return system.negate(_evaluate(formula.operand, assignment, system))
    left = _evaluate(formula.left, assignment, system)
    right = _evaluate(formula.right, assignment, system)
    operation = {Conjunction: system.conjunction, Disjunction: system.disjunction,
                 Implication: system.implication}
    return operation[type(formula)](left, right)


def evaluate(formula, assignment, system):
    validate_assignment(formula, assignment, system)
    return _evaluate(formula, assignment, system)


def interpretations(names, domain):
    count = len(domain) ** len(names)
    if count > MAX_ROWS:
        raise LogicError(f"Полный перебор не выполнен: {count} строк, лимит {MAX_ROWS}.")
    return (dict(zip(names, values)) for values in product(domain, repeat=len(names)))


@dataclass(frozen=True)
class FormulaRow:
    values: tuple[Fraction, ...]
    result: Fraction


@dataclass(frozen=True)
class FormulaAnalysis:
    names: tuple[str, ...]
    rows: tuple[FormulaRow, ...]

    @property
    def valid(self):
        return all(row.result == ONE for row in self.rows)

    @property
    def satisfiable(self):
        return any(row.result == ONE for row in self.rows)

    @property
    def identically_false(self):
        return all(row.result == ZERO for row in self.rows)

    @property
    def witness(self):
        return next((row for row in self.rows if row.result == ONE), None)

    @property
    def counterexample(self):
        return next((row for row in self.rows if row.result != ONE), None)


def analyze(formula, system):
    names = variables(formula)
    rows = tuple(FormulaRow(tuple(a[n] for n in names), _evaluate(formula, a, system))
                 for a in interpretations(names, system.domain))
    return FormulaAnalysis(names, rows)


@dataclass(frozen=True)
class SequentRow:
    values: tuple[Fraction, ...]
    premises: tuple[Fraction, ...]
    conclusion: Fraction

    @property
    def is_model(self):
        return all(value == ONE for value in self.premises)


@dataclass(frozen=True)
class EntailmentAnalysis:
    names: tuple[str, ...]
    rows: tuple[SequentRow, ...]

    @property
    def model_count(self):
        return sum(row.is_model for row in self.rows)

    @property
    def counterexample(self):
        return next((row for row in self.rows if row.is_model and row.conclusion != ONE), None)

    @property
    def entails(self):
        return self.counterexample is None

    @property
    def vacuous(self):
        return self.model_count == 0


def check_entailment(premises, conclusion, system):
    premises = tuple(premises)
    names = tuple(sorted(set().union(variables(conclusion), *(variables(p) for p in premises))))
    rows = tuple(SequentRow(tuple(a[n] for n in names),
                            tuple(_evaluate(p, a, system) for p in premises),
                            _evaluate(conclusion, a, system))
                 for a in interpretations(names, system.domain))
    return EntailmentAnalysis(names, rows)


def compare(formula, systems):
    systems = tuple(systems)
    if len(systems) < 2 or len({s.code for s in systems}) != len(systems):
        raise LogicError("Для сравнения нужны хотя бы две различные логики.")
    names = variables(formula)
    domain = tuple(sorted(set().union(*(s.domain for s in systems))))
    rows = []
    for assignment in interpretations(names, domain):
        results = tuple(_evaluate(formula, assignment, system)
                        if all(v in system.domain for v in assignment.values()) else None
                        for system in systems)
        rows.append((tuple(assignment[n] for n in names), results))
    analyses = tuple(analyze(formula, system) for system in systems)
    return names, tuple(rows), analyses
