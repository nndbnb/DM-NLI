"""Консольное приложение ЛР2: интерактивное меню или команды argparse."""

import argparse
from pathlib import Path
import sys

from logic import (LogicError, SYSTEMS, analyze, check_entailment, compare,
                   evaluate, format_formula, format_value, get_logic,
                   parse_assignments, parse_formula, validate_assignment)
from variant1 import (FORMULAS, RELATIONS, PROPERTY_HEADERS, assignment_text,
                      property_rows, render_report, table, yes)


def show_analysis(formula, system):
    analysis = analyze(formula, system)
    print(f"Формула: {format_formula(formula)}; логика: {system.code}.")
    print(table(list(analysis.names) + ["F"],
                [list(map(format_value, row.values)) + [format_value(row.result)] for row in analysis.rows]))
    print(table(PROPERTY_HEADERS, property_rows([analysis], [system])))
    if analysis.witness is not None:
        print("Пример выполнимости: " + assignment_text(analysis.names, analysis.witness.values) + "; F=1.")
    if analysis.counterexample is not None:
        row = analysis.counterexample
        print("Контрпример общезначимости: " + assignment_text(analysis.names, row.values) +
              f"; F={format_value(row.result)}.")
    if not analysis.satisfiable:
        print("Формула невыполнима: нет оценки со значением 1.")
    if analysis.identically_false:
        print("Формула тождественно ложна: на каждой оценке F=0.")


def show_comparison(formula, systems, assignment=None):
    names, rows, analyses = compare(formula, systems)
    print("Формула: " + format_formula(formula))
    if assignment is None:
        print(table(list(names) + [s.code for s in systems],
                    [list(map(format_value, vals)) +
                     [format_value(v) if v is not None else "—" for v in results]
                     for vals, results in rows]))
        print("—: оценка недопустима в данной логике.")
        differences = sum(len(set(v for v in results if v is not None)) > 1 for _, results in rows)
        print(f"Сравнимые значения совпадают во всех строках: {yes(differences == 0)}; различий: {differences}.")
    else:
        # Сначала проверяем полноту и состав оценки. Полуистина может быть
        # допустима только в части выбранных систем, что отмечается отдельно.
        allowed_domain = tuple(sorted(set().union(*(s.domain for s in systems))))
        from logic import LogicSystem
        validate_assignment(formula, assignment, LogicSystem("COMPARE", "Сравнение", allowed_domain))
        values = []
        for system in systems:
            try:
                value = evaluate(formula, assignment, system)
                values.append(value)
                print(f"{system.code}: F={format_value(value)}.")
            except LogicError as error:
                print(f"{system.code}: оценка недопустима. {error}")
        print("Совпадение значений среди допустимых систем: " +
              (yes(len(set(values)) == 1) if len(values) >= 2 else "недостаточно сравнимых систем") + ".")
    print("Свойства на полных областях соответствующих систем:")
    print(table(PROPERTY_HEADERS, property_rows(analyses, systems)))
    same = len({(a.valid, a.satisfiable, a.identically_false) for a in analyses}) == 1
    print(f"Семантические свойства совпадают: {yes(same)}.")


def show_entailment(premises, conclusion, system, show_table=False):
    result = check_entailment(premises, conclusion, system)
    print(f"Логика: {system.code}. Проверено оценок: {len(result.rows)}; моделей посылок: {result.model_count}.")
    if show_table:
        print(table(list(result.names) + [f"A{i}" for i in range(1, len(premises) + 1)] + ["B"],
                    [list(map(format_value, row.values + row.premises + (row.conclusion,))) for row in result.rows]))
    print("Логическое следование: " + ("выполняется." if result.entails else "не выполняется."))
    if result.vacuous:
        print("Посылки несовместимы: нет оценки, где все посылки равны 1. Следование выполняется формально.")
    if result.counterexample is not None:
        row = result.counterexample
        print("Контрпример: " + assignment_text(result.names, row.values) + ".")
        print(table(["Формула", "Значение"],
                    [(f"A{i}: {format_formula(p)}", format_value(v))
                     for i, (p, v) in enumerate(zip(premises, row.premises), 1)] +
                    [("B: " + format_formula(conclusion), format_value(row.conclusion))]))


def show_variant():
    systems = tuple(SYSTEMS.values())
    for name, text in FORMULAS.items():
        formula = parse_formula(text)
        print(f"\n{name}: {text}")
        print(table(PROPERTY_HEADERS, property_rows([analyze(formula, s) for s in systems], systems)))
    for name, (premises, conclusion) in RELATIONS.items():
        print(f"\n{name}: " + ", ".join(premises) + " ⊨ " + conclusion)
        for system in systems:
            show_entailment(tuple(map(parse_formula, premises)), parse_formula(conclusion), system)


def interactive():
    print("ЛР2, вариант 1. Интерпретатор C2, K3, L3.")
    print("Логики: C2 — классическая; K3 — Клини; L3 — Лукасевича.")
    while True:
        print("\n1 — значение; 2 — таблица и свойства; 3 — сравнение; 4 — следование; 5 — вариант 1; 0 — выход")
        try:
            choice = input("Режим> ").strip()
            if choice == "0":
                return
            if choice == "5":
                show_variant()
                continue
            if choice not in {"1", "2", "3", "4"}:
                print("Выберите режим от 0 до 5.")
                continue
            if choice == "4":
                texts = input("Посылки через ; (пусто — без посылок)> ").strip()
                parts = texts.split(";") if texts else []
                premises = tuple(parse_formula(p) for p in parts)
                conclusion = parse_formula(input("Заключение> "))
                system = get_logic(input("Логика C2/K3/L3> ").strip())
                show_entailment(premises, conclusion, system)
                continue
            formula = parse_formula(input("Формула> "))
            if choice == "3":
                values = input("Оценки p=1/2 q=1/2 (пусто — полный перебор)> ").strip()
                show_comparison(formula, tuple(SYSTEMS.values()), parse_assignments(values.split()) if values else None)
            else:
                system = get_logic(input("Логика C2/K3/L3> ").strip())
                if choice == "1":
                    assignment = parse_assignments(input("Оценки p=1/2 q=1/2> ").split())
                    print(f"Значение формулы: {format_value(evaluate(formula, assignment, system))}.")
                else:
                    show_analysis(formula, system)
        except LogicError as error:
            print(f"Ошибка: {error}")
        except (EOFError, KeyboardInterrupt):
            print("\nЗавершение работы.")
            return


def argument_parser():
    parser = argparse.ArgumentParser(description="ЛР2: интерпретатор C2/K3/L3, вариант 1.")
    commands = parser.add_subparsers(dest="command")
    for command in ("eval", "table", "compare"):
        p = commands.add_parser(command)
        p.add_argument("formula")
        if command == "compare":
            p.add_argument("--logics", nargs="+", default=["C2", "K3", "L3"])
        else:
            p.add_argument("--logic", default="C2")
        if command in ("eval", "compare"):
            p.add_argument("--values", nargs="+", required=command == "eval")
    p = commands.add_parser("entail")
    p.add_argument("conclusion")
    p.add_argument("--premise", action="append", default=[])
    p.add_argument("--logic", default="C2")
    p.add_argument("--table", action="store_true")
    commands.add_parser("variant")
    p = commands.add_parser("report")
    p.add_argument("--output", type=Path)
    return parser


def main(argv=None):
    args = argument_parser().parse_args(argv)
    try:
        if args.command is None:
            interactive()
        elif args.command == "report":
            text = render_report()
            if args.output is None:
                print(text)
            else:
                args.output.write_text(text, encoding="utf-8")
                print("Отчёт сохранён: " + str(args.output))
        elif args.command == "variant":
            show_variant()
        elif args.command == "entail":
            show_entailment(tuple(map(parse_formula, args.premise)), parse_formula(args.conclusion),
                            get_logic(args.logic), args.table)
        else:
            formula = parse_formula(args.formula)
            if args.command == "eval":
                system = get_logic(args.logic)
                assignment = parse_assignments(args.values)
                print(f"{system.code}: {format_formula(formula)} = {format_value(evaluate(formula, assignment, system))}")
            elif args.command == "table":
                show_analysis(formula, get_logic(args.logic))
            else:
                systems = tuple(get_logic(code) for code in args.logics)
                show_comparison(formula, systems, parse_assignments(args.values) if args.values else None)
        return 0
    except (LogicError, OSError) as error:
        print(f"Ошибка: {error}", file=sys.stderr)
        return 2


if __name__ == "__main__":
    sys.exit(main())
