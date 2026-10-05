from __future__ import annotations

from dataclasses import dataclass
from typing import Optional, Union
import re


# ============================================================
# 1. Абстрактное синтаксическое дерево (AST)
# ============================================================


@dataclass(frozen=True)
class Variable:
    name: str


@dataclass(frozen=True)
class FalseConst:
    pass


@dataclass(frozen=True)
class Implication:
    left: "Formula"
    right: "Formula"


Formula = Union[Variable, FalseConst, Implication]
FALSE = FalseConst()


# ============================================================
# 2. Синтаксический анализатор
# ============================================================


class FormulaSyntaxError(ValueError):
    pass


TOKEN_RE = re.compile(r"[A-Za-z][A-Za-z0-9_]*|[()⊃]")


def normalize(text: str) -> str:
    """Разрешаем несколько удобных записей импликации."""
    return (
        text.strip()
        .replace("→", "⊃")
        .replace("⇒", "⊃")
        .replace("=>", "⊃")
        .replace("->", "⊃")
    )


def tokenize(text: str) -> list[str]:
    text = normalize(text)
    tokens: list[str] = []
    pos = 0

    while pos < len(text):
        if text[pos].isspace():
            pos += 1
            continue

        match = TOKEN_RE.match(text, pos)
        if match is None:
            raise FormulaSyntaxError(
                f"Недопустимый символ '{text[pos]}' в позиции {pos + 1}. "
                "Для варианта 1 разрешены переменные, f, скобки и импликация ⊃ (или ->)."
            )

        tokens.append(match.group(0))
        pos = match.end()

    if not tokens:
        raise FormulaSyntaxError("Пустая строка не является формулой.")

    return tokens


class Parser:
    """
    Грамматика записи ППФ для варианта 1:

        expression ::= atom (⊃ atom)*
        atom ::= f | variable | (expression)

    Согласно слайду 16 лекции 1, цепочки импликаций разбираются слева:
        p⊃q⊃r = (p⊃q)⊃r
    Скобки позволяют задать другую группировку: p⊃(q⊃r).
    """

    def __init__(self, tokens: list[str]):
        self.tokens = tokens
        self.pos = 0

    def current(self) -> Optional[str]:
        if self.pos >= len(self.tokens):
            return None
        return self.tokens[self.pos]

    def take(self, expected: Optional[str] = None) -> str:
        token = self.current()
        if token is None:
            raise FormulaSyntaxError("Неожиданный конец формулы.")
        if expected is not None and token != expected:
            raise FormulaSyntaxError(
                f"Ожидался символ '{expected}', получен '{token}'."
            )
        self.pos += 1
        return token

    def parse_parenthesized_or_atom(self) -> Formula:
        token = self.current()

        if token is None:
            raise FormulaSyntaxError("Ожидалась формула, но строка закончилась.")

        if token == "(":
            self.take("(")
            formula = self.parse_expression()
            self.take(")")
            return formula

        if token in {"⊃", ")"}:
            raise FormulaSyntaxError(f"Ожидалась формула, получен символ '{token}'.")

        name = self.take()
        if name == "f":
            return FALSE
        return Variable(name)

    def parse_expression(self) -> Formula:
        result = self.parse_parenthesized_or_atom()
        # Каждый следующий антецедент - вся уже разобранная левая часть.
        while self.current() == "⊃":
            self.take("⊃")
            right = self.parse_parenthesized_or_atom()
            result = Implication(result, right)
        return result

    def parse(self) -> Formula:
        result = self.parse_expression()
        if self.current() is not None:
            tail = " ".join(self.tokens[self.pos :])
            raise FormulaSyntaxError(f"Лишняя часть выражения: '{tail}'.")

        return result


def parse_formula(text: str) -> Formula:
    return Parser(tokenize(text)).parse()


# ============================================================
# 3. Печать AST обратно в привычной форме
# ============================================================


def formula_to_string(formula: Formula, nested: bool = False) -> str:
    if isinstance(formula, Variable):
        return formula.name
    if isinstance(formula, FalseConst):
        return "f"

    left = formula_to_string(formula.left, nested=True)
    right = formula_to_string(formula.right, nested=True)
    text = f"{left}⊃{right}"
    return f"({text})" if nested else text


# ============================================================
# 4. Правило beta: одна подстановка за один шаг
# ============================================================


def variables_in(formula: Formula) -> set[str]:
    if isinstance(formula, Variable):
        return {formula.name}
    if isinstance(formula, FalseConst):
        return set()
    return variables_in(formula.left) | variables_in(formula.right)


def try_beta_for_variable(
    source: Formula, target: Formula, variable: str
) -> Optional[Formula]:
    """
    Проверяет, можно ли получить target из source одной полной подстановкой
    некоторой формулы X вместо ВСЕХ вхождений переменной variable.

    Если можно, возвращает X, иначе None.
    """

    replacement: Optional[Formula] = None

    def match(src: Formula, dst: Formula) -> bool:
        nonlocal replacement

        if isinstance(src, Variable) and src.name == variable:
            if replacement is None:
                replacement = dst
                return True
            return replacement == dst

        if type(src) is not type(dst):
            return False

        if isinstance(src, Variable):
            return src.name == dst.name  # type: ignore[attr-defined]

        if isinstance(src, FalseConst):
            return True

        # Здесь обе формулы -- Implication.
        assert isinstance(src, Implication)
        assert isinstance(dst, Implication)
        return match(src.left, dst.left) and match(src.right, dst.right)

    if variable not in variables_in(source):
        return None

    if not match(source, target):
        return None

    return replacement


def find_beta(source: Formula, target: Formula) -> Optional[tuple[str, Formula]]:
    # Нулевую "подстановку переменной самой на себя" не считаем новым шагом.
    if source == target:
        return None

    for variable in sorted(variables_in(source)):
        replacement = try_beta_for_variable(source, target, variable)
        if replacement is not None:
            return variable, replacement

    return None


# ============================================================
# 5. Верификатор доказательства
# ============================================================


@dataclass
class SourceRef:
    formula: Formula
    description: str


@dataclass
class ProofLine:
    number: int
    formula: Formula
    reason: str


class ProofVerifier:
    def __init__(self) -> None:
        # Вариант 1 из задания.
        self.axioms: list[tuple[str, Formula]] = [
            ("A1", parse_formula("p⊃(q⊃p)")),
            ("A2", parse_formula("(s⊃(p⊃q))⊃((s⊃p)⊃(s⊃q))")),
            ("A3", parse_formula("((p⊃f)⊃f)⊃p")),
        ]
        self.rules = ("MP", "β")
        self.proof: list[ProofLine] = []

    def all_sources(self) -> list[SourceRef]:
        # По условию лабораторной доступны аксиомы и предыдущие формулы.
        # Новая проверяемая формула ещё не входит в источники вывода.
        axioms = [
            SourceRef(formula, f"аксиома {name}") for name, formula in self.axioms
        ]
        previous_lines = [
            SourceRef(line.formula, f"строка {line.number}") for line in self.proof
        ]
        return axioms + previous_lines

    def find_axiom(self, formula: Formula) -> Optional[str]:
        for name, axiom in self.axioms:
            if formula == axiom:
                return name
        return None

    def find_mp(
        self, target: Formula
    ) -> Optional[tuple[SourceRef, SourceRef]]:
        sources = self.all_sources()

        # Для быстрого поиска формул A среди доступных источников.
        by_formula: dict[Formula, SourceRef] = {}
        for source in sources:
            by_formula.setdefault(source.formula, source)

        for implication_source in sources:
            formula = implication_source.formula
            if not isinstance(formula, Implication):
                continue
            if formula.right != target:
                continue

            antecedent_source = by_formula.get(formula.left)
            if antecedent_source is not None:
                return implication_source, antecedent_source

        return None

    def find_beta_step(
        self, target: Formula
    ) -> Optional[tuple[SourceRef, str, Formula]]:
        for source in self.all_sources():
            result = find_beta(source.formula, target)
            if result is not None:
                variable, replacement = result
                return source, variable, replacement
        return None

    def already_proved(self, formula: Formula) -> Optional[int]:
        for line in self.proof:
            if line.formula == formula:
                return line.number
        return None

    def verify(self, text: str) -> tuple[bool, str]:
        try:
            formula = parse_formula(text)
        except FormulaSyntaxError as error:
            return False, f"Ошибка: строка не является ППФ. {error}"

        existing = self.already_proved(formula)
        if existing is not None:
            return True, f"Формула уже была доказана ранее (строка {existing})."

        axiom_name = self.find_axiom(formula)
        if axiom_name is not None:
            reason = f"аксиома {axiom_name}"
            self._append(formula, reason)
            return True, (
                f"Формула {formula_to_string(formula)} является {reason} "
                "и добавлена в список выведенных формул."
            )

        mp = self.find_mp(formula)
        if mp is not None:
            implication_source, antecedent_source = mp
            implication = implication_source.formula
            assert isinstance(implication, Implication)

            reason = (
                "modus ponens из "
                f"{implication_source.description} и {antecedent_source.description}"
            )
            self._append(formula, reason)

            return True, (
                f"Формула {formula_to_string(formula)} выводима из формул "
                f"{formula_to_string(implication)} и "
                f"{formula_to_string(implication.left)} по правилу modus ponens. "
                "Формула добавлена в список выведенных формул."
            )

        beta = self.find_beta_step(formula)
        if beta is not None:
            source, variable, replacement = beta
            reason = (
                f"β из {source.description}: "
                f"[{formula_to_string(replacement)}/{variable}]"
            )
            self._append(formula, reason)

            return True, (
                f"Формула {formula_to_string(formula)} выводима из формулы "
                f"{formula_to_string(source.formula)} по правилу β с подстановкой "
                f"формулы {formula_to_string(replacement)} вместо переменной {variable}. "
                "Формула добавлена в список выведенных формул."
            )

        return False, (
            f"Формула {formula_to_string(formula)} является ППФ, но на текущем шаге "
            "не выводится ни как аксиома, ни по modus ponens, ни одной β-подстановкой "
            "из доступных формул."
        )

    def _append(self, formula: Formula, reason: str) -> None:
        self.proof.append(
            ProofLine(number=len(self.proof) + 1, formula=formula, reason=reason)
        )

    def show_axioms(self) -> str:
        lines = ["Аксиомы варианта 1:"]
        for name, formula in self.axioms:
            lines.append(f"  {name}: {formula_to_string(formula)}")
        return "\n".join(lines)

    def show_proof(self) -> str:
        if not self.proof:
            return "Список выведенных формул пока пуст."

        lines = ["Выведенные формулы:"]
        for line in self.proof:
            lines.append(
                f"  {line.number}. {formula_to_string(line.formula)}    [{line.reason}]"
            )
        return "\n".join(lines)

    def clear(self) -> None:
        self.proof.clear()


# ============================================================
# 6. Консольный интерфейс
# ============================================================


HELP = """Команды:
  axioms  - показать аксиомы варианта 1
  list    - показать уже выведенные формулы
  clear   - очистить текущий сеанс доказательства
  help    - показать эту справку
  exit    - завершить программу

Ввод формул:
  импликация: ⊃, ->, => или →
  ложь:       f
  переменные: латинские идентификаторы, например p, q, s, x1

Примеры ППФ:
  p⊃(q⊃p)
  (s⊃(p⊃q))⊃((s⊃p)⊃(s⊃q))
  ((p⊃f)⊃f)⊃p

Без скобок импликации группируются слева: p⊃q⊃r = (p⊃q)⊃r.
Для группировки справа используйте скобки: p⊃(q⊃r).
Аксиомы доступны для MP и β с начала сеанса.
"""


def main() -> None:
    verifier = ProofVerifier()

    print("Верификатор доказательств — лабораторная работа №1, вариант 1")
    print("Операции варианта: импликация ⊃; правила: MP и β.")
    print("Введите help для справки.\n")

    while True:
        try:
            raw = input("formula> ").strip()
        except (EOFError, KeyboardInterrupt):
            print("\nЗавершение работы.")
            break

        if not raw:
            continue

        command = raw.lower()
        if command in {"exit", "quit"}:
            print("Завершение работы.")
            break
        if command == "help":
            print(HELP)
            continue
        if command == "axioms":
            print(verifier.show_axioms())
            continue
        if command == "list":
            print(verifier.show_proof())
            continue
        if command == "clear":
            verifier.clear()
            print("Список выведенных формул очищен.")
            continue

        _, message = verifier.verify(raw)
        print(message)


if __name__ == "__main__":
    main()
