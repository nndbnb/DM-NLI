"""Синтаксис и семантика классической логики, K3 и L3. Только стандартная библиотека."""

from dataclasses import dataclass
from fractions import Fraction
from itertools import product
import re
from typing import Mapping, Optional


ZERO, HALF, ONE = Fraction(0), Fraction(1, 2), Fraction(1)
MAX_INPUT_LENGTH = 10000
MAX_DEPTH = 80
MAX_ROWS = 100000


class LogicError(ValueError):
    """Ошибка ввода или ограничение размера задачи."""


class FormulaSyntaxError(LogicError):
    pass


@dataclass(frozen=True)
class Node:
    kind: str
    name: str = ""
    left: Optional["Node"] = None
    right: Optional["Node"] = None


TOKEN = re.compile(r"[A-Za-z][A-Za-z0-9_]*|[()¬∧∨→]")
ALIASES = (("->", "→"), ("=>", "→"), ("⊃", "→"), ("⇒", "→"),
           ("&&", "∧"), ("||", "∨"), ("&", "∧"), ("|", "∨"),
           ("!", "¬"), ("~", "¬"))


def tokenize(text: str) -> list[str]:
    if len(text) > MAX_INPUT_LENGTH:
        raise LogicError(f"Формула не проверена: больше {MAX_INPUT_LENGTH} символов.")
    for old, new in ALIASES:
        text = text.replace(old, new)
    tokens, pos = [], 0
    while pos < len(text):
        if text[pos].isspace():
            pos += 1
            continue
        match = TOKEN.match(text, pos)
        if not match:
            raise FormulaSyntaxError(f"Недопустимый символ {text[pos]!r}, позиция {pos + 1}.")
        tokens.append(match.group())
        pos = match.end()
    if not tokens:
        raise FormulaSyntaxError("Пустая строка не является формулой.")
    return tokens


class Parser:
    """Приоритеты: ¬ > ∧ > ∨ > →. Цепочки → группируются слева, как в ЛР1."""

    def __init__(self, text: str):
        self.tokens = tokenize(text)
        self.pos = 0
        self.nesting = 0

    def current(self):
        return self.tokens[self.pos] if self.pos < len(self.tokens) else None

    def take(self, expected=None):
        token = self.current()
        if token is None:
            raise FormulaSyntaxError("Неожиданный конец формулы.")
        if expected is not None and token != expected:
            raise FormulaSyntaxError(f"Ожидалось {expected!r}, получено {token!r}.")
        self.pos += 1
        return token

    def binary(self, operand, token, kind):
        result = operand()
        while self.current() == token:
            self.take()
            result = Node(kind, left=result, right=operand())
        return result

    def implication(self):
        return self.binary(self.disjunction, "→", "imp")

    def disjunction(self):
        return self.binary(self.conjunction, "∨", "or")

    def conjunction(self):
        return self.binary(self.unary, "∧", "and")

    def unary(self):
        token = self.current()
        if token in ("¬", "("):
            self.nesting += 1
            if self.nesting > MAX_DEPTH:
                raise LogicError(f"Формула не проверена: больше {MAX_DEPTH} уровней вложенности.")
            self.take()
            if token == "¬":
                result = Node("not", left=self.unary())
            else:
                result = self.implication()
                self.take(")")
            self.nesting -= 1
            return result
        if token is None or token in ("∧", "∨", "→", ")"):
            raise FormulaSyntaxError(f"Ожидалась переменная, отрицание или скобка; получено {token!r}.")
        return Node("var", name=self.take())

    def parse(self):
        result = self.implication()
        if self.current() is not None:
            raise FormulaSyntaxError(f"Лишняя часть выражения: {' '.join(self.tokens[self.pos:])}.")
        pending = [(result, 0)]
        while pending:
            node, depth = pending.pop()
            if depth > MAX_DEPTH:
                raise LogicError(f"Формула не проверена: глубина дерева больше {MAX_DEPTH}.")
            for child in (node.left, node.right):
                if child is not None:
                    pending.append((child, depth + 1))
        return result


def parse_formula(text: str) -> Node:
    return Parser(text).parse()


def variables(formula: Node) -> tuple[str, ...]:
    names, pending = set(), [formula]
    while pending:
        node = pending.pop()
        if node.kind == "var":
            names.add(node.name)
        pending.extend(child for child in (node.left, node.right) if child is not None)
    return tuple(sorted(names))


def format_formula(formula: Node, nested=False) -> str:
    if formula.kind == "var":
        return formula.name
    if formula.kind == "not":
        return "¬" + format_formula(formula.left, True)
    symbol = {"and": "∧", "or": "∨", "imp": "→"}[formula.kind]
    text = format_formula(formula.left, True) + symbol + format_formula(formula.right, True)
    return "(" + text + ")" if nested else text


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
    if formula.kind == "var":
        return assignment[formula.name]
    left = _evaluate(formula.left, assignment, system)
    if formula.kind == "not":
        return system.negate(left)
    right = _evaluate(formula.right, assignment, system)
    operation = {"and": system.conjunction, "or": system.disjunction, "imp": system.implication}
    return operation[formula.kind](left, right)


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
