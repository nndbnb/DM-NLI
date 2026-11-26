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


@dataclass(frozen=True)
class Negation:
    operand: "Formula"


@dataclass(frozen=True)
class Conjunction:
    left: "Formula"
    right: "Formula"


@dataclass(frozen=True)
class Disjunction:
    left: "Formula"
    right: "Formula"


Formula = Union[Variable, FalseConst, Implication, Negation, Conjunction, Disjunction]
FALSE = FalseConst()


def formula_children(formula: Formula) -> tuple[Formula, ...]:
    """Общий обход AST для парсера, схем аксиом, β и семантики ЛР2."""
    if isinstance(formula, (Variable, FalseConst)):
        return ()
    if isinstance(formula, Negation):
        return (formula.operand,)
    return (formula.left, formula.right)


# ============================================================
# 2. Синтаксический анализатор
# ============================================================


class FormulaError(ValueError):
    """Общая ошибка формул для обеих лабораторных."""


class FormulaSyntaxError(FormulaError):
    pass


class FormulaLimitError(FormulaError):
    """Ввод не проверен из-за ограничения ресурсов, а не ошибки ППФ."""


MAX_INPUT_LENGTH = 20000
MAX_FORMULA_DEPTH = 100
TOKEN_RE = re.compile(r"[A-Za-z][A-Za-z0-9_]*|[()⊃]")
EXTENDED_TOKEN_RE = re.compile(r"[A-Za-z][A-Za-z0-9_]*|[()⊃¬∧∨]")


def normalize(text: str, extended: bool = False) -> str:
    """Разрешаем несколько удобных записей импликации."""
    result = (
        text.strip()
        .replace("→", "⊃")
        .replace("⇒", "⊃")
        .replace("=>", "⊃")
        .replace("->", "⊃")
    )
    if extended:
        for old, new in (("&&", "∧"), ("||", "∨"), ("&", "∧"), ("|", "∨"), ("!", "¬"), ("~", "¬")):
            result = result.replace(old, new)
    return result


def tokenize(text: str, extended: bool = False) -> list[str]:
    if len(text) > MAX_INPUT_LENGTH:
        raise FormulaLimitError(
            f"Превышен лимит длины ввода ({MAX_INPUT_LENGTH} символов)."
        )
    text = normalize(text, extended)
    token_re = EXTENDED_TOKEN_RE if extended else TOKEN_RE
    tokens: list[str] = []
    pos = 0

    while pos < len(text):
        if text[pos].isspace():
            pos += 1
            continue

        match = token_re.match(text, pos)
        if match is None:
            allowed = ("В расширенном режиме разрешены переменные, f, скобки, ¬, ∧, ∨ и ⊃ (или ->)."
                       if extended else "Для варианта 1 разрешены переменные, f, скобки и импликация ⊃ (или ->).")
            raise FormulaSyntaxError(
                f"Недопустимый символ '{text[pos]}' в позиции {pos + 1}. "
                + allowed
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
    Для ЛР2 extended=True добавляет приоритеты ¬ > ∧ > ∨ > ⊃.
    По умолчанию сохраняется язык варианта 1 ЛР1: только импликация и f.
    """

    def __init__(self, tokens: list[str], extended: bool = False):
        self.tokens = tokens
        self.pos = 0
        self.nesting = 0
        self.extended = extended

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
            if self.nesting >= MAX_FORMULA_DEPTH:
                raise FormulaLimitError(
                    f"Превышен лимит вложенности скобок ({MAX_FORMULA_DEPTH})."
                )
            self.take("(")
            self.nesting += 1
            formula = self.parse_expression()
            self.take(")")
            self.nesting -= 1
            return formula

        if token in {"⊃", ")", "¬", "∧", "∨"}:
            raise FormulaSyntaxError(f"Ожидалась формула, получен символ '{token}'.")

        name = self.take()
        if name == "f":
            return FALSE
        return Variable(name)

    def parse_expression(self) -> Formula:
        operand = self.parse_disjunction if self.extended else self.parse_parenthesized_or_atom
        result = operand()
        # Каждый следующий антецедент - вся уже разобранная левая часть.
        while self.current() == "⊃":
            self.take("⊃")
            right = operand()
            result = Implication(result, right)
        return result

    def parse_disjunction(self) -> Formula:
        result = self.parse_conjunction()
        while self.current() == "∨":
            self.take("∨")
            result = Disjunction(result, self.parse_conjunction())
        return result

    def parse_conjunction(self) -> Formula:
        result = self.parse_unary()
        while self.current() == "∧":
            self.take("∧")
            result = Conjunction(result, self.parse_unary())
        return result

    def parse_unary(self) -> Formula:
        if self.current() == "¬":
            if self.nesting >= MAX_FORMULA_DEPTH:
                raise FormulaLimitError(
                    f"Превышен лимит вложенности операций ({MAX_FORMULA_DEPTH})."
                )
            self.take("¬")
            self.nesting += 1
            result = Negation(self.parse_unary())
            self.nesting -= 1
            return result
        return self.parse_parenthesized_or_atom()

    def parse(self) -> Formula:
        result = self.parse_expression()
        if self.current() is not None:
            tail = " ".join(self.tokens[self.pos :])
            raise FormulaSyntaxError(f"Лишняя часть выражения: '{tail}'.")

        # Цепочка без скобок тоже может создать слишком глубокое дерево.
        pending = [(result, 0)]
        while pending:
            node, depth = pending.pop()
            if depth > MAX_FORMULA_DEPTH:
                raise FormulaLimitError(
                    f"Превышен лимит глубины дерева ({MAX_FORMULA_DEPTH})."
                )
            pending.extend((child, depth + 1) for child in formula_children(node))

        return result


def parse_formula(text: str, extended: bool = False) -> Formula:
    return Parser(tokenize(text, extended), extended).parse()


# ============================================================
# 3. Печать AST обратно в привычной форме
# ============================================================


def formula_to_string(formula: Formula, nested: bool = False) -> str:
    if isinstance(formula, Variable):
        return formula.name
    if isinstance(formula, FalseConst):
        return "f"
    if isinstance(formula, Negation):
        return "¬" + formula_to_string(formula.operand, nested=True)

    left = formula_to_string(formula.left, nested=True)
    right = formula_to_string(formula.right, nested=True)
    symbol = {Implication: "⊃", Conjunction: "∧", Disjunction: "∨"}[type(formula)]
    text = f"{left}{symbol}{right}"
    return f"({text})" if nested else text


# ============================================================
# 4. Правило beta: одна подстановка за один шаг
# ============================================================


def variables_in(formula: Formula) -> set[str]:
    if isinstance(formula, Variable):
        return {formula.name}
    if isinstance(formula, FalseConst):
        return set()
    return set().union(*(variables_in(child) for child in formula_children(formula)))


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

        return all(match(a, b) for a, b in zip(formula_children(src), formula_children(dst)))

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
# 5. Сопоставление со схемой аксиомы
# ============================================================


def match_axiom_schema(
    schema: Formula, formula: Formula
) -> Optional[dict[str, Formula]]:
    """Сопоставляет маски схемы с целыми поддеревьями проверяемой формулы.

    Разные маски независимы и могут совпадать друг с другом. Все вхождения
    одной маски обязаны соответствовать одному и тому же дереву. Имена
    переменных внутри найденного дерева не интерпретируются повторно.
    Константа f и узлы импликации самой схемы остаются фиксированными.
    Это распознавание экземпляра схемы, а не шаг β-подстановки.
    """
    bindings: dict[str, Formula] = {}

    def match(pattern: Formula, target: Formula) -> bool:
        if isinstance(pattern, Variable):
            if pattern.name not in bindings:
                bindings[pattern.name] = target
                return True
            return bindings[pattern.name] == target
        if isinstance(pattern, FalseConst):
            return isinstance(target, FalseConst)
        if type(pattern) is not type(target):
            return False
        return all(match(a, b) for a, b in zip(formula_children(pattern), formula_children(target)))

    return bindings if match(schema, formula) else None


def instantiate_axiom_schema(
    schema: Formula, bindings: dict[str, Formula]
) -> Optional[Formula]:
    """Собирает экземпляр без повторной подстановки внутри привязок масок.

    Непривязанная маска означает, что ограничения не определили экземпляр.
    Её нельзя молча считать конкретной переменной с тем же именем.
    """
    if isinstance(schema, Variable):
        return bindings.get(schema.name)
    if isinstance(schema, FalseConst):
        return FALSE
    children = [instantiate_axiom_schema(child, bindings)
                for child in formula_children(schema)]
    if any(child is None for child in children):
        return None
    return type(schema)(*children)


# ============================================================
# 6. Верификатор доказательства
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
        # Схемы аксиом варианта 1. Их переменные являются масками поддеревьев.
        self.axioms: list[tuple[str, Formula]] = [
            ("A1", parse_formula("p⊃(q⊃p)")),
            ("A2", parse_formula("(s⊃(p⊃q))⊃((s⊃p)⊃(s⊃q))")),
            ("A3", parse_formula("((p⊃f)⊃f)⊃p")),
        ]
        self.rules = ("MP", "β")
        self.proof: list[ProofLine] = []

    def all_sources(self) -> list[SourceRef]:
        # Конечные явно заданные источники для MP и β.
        # Остальные экземпляры схем для MP строятся по цели в find_mp().
        # Новая проверяемая формула ещё не входит в источники вывода.
        axioms = [
            SourceRef(formula, f"аксиомы {name}") for name, formula in self.axioms
        ]
        previous_lines = [
            SourceRef(line.formula, f"строки {line.number}") for line in self.proof
        ]
        return axioms + previous_lines

    def find_axiom(self, formula: Formula) -> Optional[str]:
        for name, axiom in self.axioms:
            if match_axiom_schema(axiom, formula) is not None:
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

        def available(formula: Formula) -> Optional[SourceRef]:
            source = by_formula.get(formula)
            if source is not None:
                return source
            name = self.find_axiom(formula)
            if name is not None:
                return SourceRef(formula, f"экземпляра схемы аксиомы {name}")
            return None

        # Сохраняем предпочтение уже имеющихся посылок и обоснований.
        # Меньшая посылка также может быть не введённым экземпляром схемы.
        for implication_source in sources:
            formula = implication_source.formula
            if not isinstance(formula, Implication):
                continue
            if formula.right != target:
                continue

            antecedent_source = available(formula.left)
            if antecedent_source is not None:
                return implication_source, antecedent_source

        # У всех схем варианта 1 каждая маска встречается в консеквенте.
        # Сопоставление с целью однозначно задаёт нужный экземпляр большей
        # посылки: бесконечный перебор аксиом и поиск многошагового вывода
        # не нужны. Посылки не добавляются в историю автоматически.
        for name, schema in self.axioms:
            if not isinstance(schema, Implication):
                continue
            bindings = match_axiom_schema(schema.right, target)
            if bindings is None:
                continue
            implication = instantiate_axiom_schema(schema, bindings)
            if not isinstance(implication, Implication):
                continue
            antecedent_source = available(implication.left)
            if antecedent_source is not None:
                return (SourceRef(implication, f"экземпляра схемы аксиомы {name}"),
                        antecedent_source)

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
        except FormulaLimitError as error:
            return False, f"Формула не проверена: {error} Упростите ввод."
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
                f"Формула {formula_to_string(formula)} является экземпляром схемы аксиомы {axiom_name} "
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

        missing = []
        for source in self.all_sources():
            candidate = source.formula
            if isinstance(candidate, Implication) and candidate.right == formula:
                antecedent = formula_to_string(candidate.left)
                if antecedent not in missing:
                    missing.append(antecedent)

        if len(missing) == 1:
            mp_detail = f"Для modus ponens не хватает посылки {missing[0]}."
        elif missing:
            mp_detail = (
                "Для modus ponens нужна хотя бы одна из недостающих посылок: "
                + "; ".join(missing) + "."
            )
        else:
            mp_detail = (
                "Для modus ponens не найдены обе посылки A⊃B и A с заключением "
                f"{formula_to_string(formula)}."
            )
        return False, (
            f"Формула {formula_to_string(formula)} является ППФ (синтаксис корректен).\n"
            "Шаг не принят: не найдено обоснование схемой аксиомы, modus ponens "
            "или одной β-подстановкой.\n"
            + mp_detail + "\n"
            "Проверяется один шаг. Отказ не означает ошибку ППФ или отсутствие полного доказательства."
        )

    def _append(self, formula: Formula, reason: str) -> None:
        self.proof.append(
            ProofLine(number=len(self.proof) + 1, formula=formula, reason=reason)
        )

    def show_axioms(self) -> str:
        lines = ["Схемы аксиом варианта 1 (переменные — маски поддеревьев):"]
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
# 7. Консольный интерфейс
# ============================================================


HELP = """Команды:
  axioms  - показать схемы аксиом варианта 1
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
Переменные в схемах аксиом — маски для произвольных поддеревьев.
Повтор одной маски требует одинакового дерева. Константа f не является маской.
Для MP доступны также не введённые экземпляры схем аксиом в обеих посылках.
Соответствие схеме аксиомы проверяется раньше MP и β.
Проверяется только один шаг, а не существование полного доказательства.
Повтор формулы не добавляет строку. clear удаляет ранее введённые шаги.
Лимиты: 20000 символов, 100 уровней скобок и 100 уровней дерева.
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
