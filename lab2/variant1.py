"""Примеры варианта 1 и формирование воспроизводимого отчёта."""

from logic import SYSTEMS, check_entailment, compare, format_value, parse_formula


FORMULAS = {
    "F1": "(p → q) ∨ (q → p)",
    "F2": "((p → q) → p) → p",
    "F3": "(p ∧ ¬p) ∨ q",
    "F4": "(p ∧ ¬p) ∧ q",
    "F5": "((p → q) ∧ (q → r)) → (p → r)",
}
RELATIONS = {
    "R1": (["p ∨ q", "p → r", "q → r", "r → s", "s → t"], "t"),
    "R2": (["p → q", "p → r", "(q ∧ r) → s", "s → t", "t → u"], "¬p ∨ u"),
    "R3": (["p ∨ q", "p → r", "q → s", "r → t", "s → t"], "t ∧ (p ∨ ¬p)"),
    "R4": (["p ∨ q", "p → r", "q → s", "(r ∨ s) → t", "s → u"], "t → u"),
}


def yes(value):
    return "да" if value else "нет"


def table(headers, rows):
    return "\n".join([
        "| " + " | ".join(str(x) for x in headers) + " |",
        "| " + " | ".join("---" for _ in headers) + " |",
    ] + ["| " + " | ".join(str(x) for x in row) + " |" for row in rows])


def assignment_text(names, values):
    return ", ".join(f"{n}={format_value(v)}" for n, v in zip(names, values))


def property_rows(analyses, systems):
    return [(s.code, len(a.rows), yes(a.valid), yes(a.satisfiable), yes(a.identically_false))
            for s, a in zip(systems, analyses)]


PROPERTY_HEADERS = ["Логика", "Оценок", "Общезначима", "Выполнима", "Тождественно ложна"]


def render_report():
    systems = tuple(SYSTEMS.values())
    out = [
        "# Лабораторная работа 2. Вариант 1\n",
        "Тема: интерпретатор многозначных логик и проверка семантических свойств формул.\n",
        "## Метод проверки\n",
        "Использован полный перебор допустимых оценок. C2: {0, 1}; K3 и L3: {0, 1/2, 1}. "
        "Выделено только значение 1. Общезначимость: F=1 на всех оценках. "
        "Выполнимость: существует оценка с F=1. Тождественная ложность: F=0 на всех оценках.\n",
        "Операции: ¬a=1−a, a∧b=min(a,b), a∨b=max(a,b). "
        "В C2 и K3: a→b=max(1−a,b). В L3: a→b=min(1,1−a+b). "
        "Вычисления выполняются точными рациональными числами Fraction.\n",
        "Следование нарушается, если все посылки равны 1, а вывод равен 0 или 1/2. "
        "При отсутствии совместной модели посылок следование выполняется формально; "
        "программа отдельно сообщает, что посылки несовместимы.\n",
        "Порядок перебора: имена переменных по алфавиту, значения по возрастанию. "
        "В качестве примера или контрпримера приводится первая подходящая оценка.\n",
        "## Задание 1. Формулы\n",
    ]
    for label, text in FORMULAS.items():
        formula = parse_formula(text)
        names, rows, analyses = compare(formula, systems)
        out += [f"### {label}\n", f"`{text}`\n", table(PROPERTY_HEADERS, property_rows(analyses, systems)), "",
                "Полная таблица значений:\n",
                table(list(names) + list(SYSTEMS),
                      [list(map(format_value, values)) +
                       [format_value(v) if v is not None else "—" for v in results]
                       for values, results in rows]), "",
                "Знак — означает, что оценка с 1/2 недопустима в C2.\n"]
        differences = sum(len(set(v for v in results if v is not None)) > 1 for _, results in rows)
        props_equal = len({(a.valid, a.satisfiable, a.identically_false) for a in analyses}) == 1
        out += [f"Сравнимые значения во всех строках совпадают: {yes(differences == 0)}. "
                f"Различающихся строк: {differences}. Семантические свойства совпадают: {yes(props_equal)}.\n"]
        for system, analysis in zip(systems, analyses):
            witness = analysis.witness
            counter = analysis.counterexample
            out.append(f"- {system.code}: " +
                       (f"пример выполнимости: {assignment_text(names, witness.values)}, F=1; "
                        if witness else "оценок со значением 1 нет; ") +
                       (f"контрпример общезначимости: {assignment_text(names, counter.values)}, "
                        f"F={format_value(counter.result)}." if counter else "контрпримеров общезначимости нет."))
        out.append("")
    out += ["## Задание 2. Логическое следование\n"]
    for label, (premise_texts, conclusion_text) in RELATIONS.items():
        premises = tuple(map(parse_formula, premise_texts))
        conclusion = parse_formula(conclusion_text)
        out += [f"### {label}\n", "`" + ", ".join(premise_texts) + " ⊨ " + conclusion_text + "`\n"]
        analyses = [check_entailment(premises, conclusion, s) for s in systems]
        out += [table(["Логика", "Всего оценок", "Моделей посылок", "Следование", "Посылки несовместимы"],
                      [(s.code, len(a.rows), a.model_count, yes(a.entails), yes(a.vacuous))
                       for s, a in zip(systems, analyses)]), ""]
        for system, analysis in zip(systems, analyses):
            row = analysis.counterexample
            if row is not None:
                out += [f"Контрпример для {system.code}: {assignment_text(analysis.names, row.values)}.\n",
                        table(["Формула", "Значение"],
                              [(f"A{i}: {text}", format_value(value))
                               for i, (text, value) in enumerate(zip(premise_texts, row.premises), 1)] +
                              [(f"B: {conclusion_text}", format_value(row.conclusion))]), ""]
            elif analysis.vacuous:
                out.append(f"{system.code}: совместных моделей посылок нет; следование формальное.\n")
            else:
                out.append(f"{system.code}: проверены все {len(analysis.rows)} оценок; "
                           f"среди {analysis.model_count} моделей посылок контрпримеров нет.\n")
    out += [
        "## Выводы\n",
        "F1 общезначима в C2 и L3, но не в K3. F2 общезначима только в C2. "
        "F3 выполнима и не общезначима во всех трёх системах. "
        "F4 невыполнима во всех системах, но тождественно ложна только в C2: "
        "при p=q=1/2 в K3 и L3 она равна 1/2. F5 общезначима в C2, "
        "но имеет контрпримеры в K3 и L3.\n",
        "R1 выполняется во всех системах. R2 выполняется в C2 и K3, "
        "но нарушается в L3. R3 выполняется в C2 и нарушается в K3 и L3. "
        "R4 нарушается во всех системах. Для всех четырёх отношений "
        "во всех системах существуют совместные модели посылок.\n",
        "## Воспроизведение\n",
        "Из корня репозитория:\n",
        '```bash\npython lab2/lab2_variant1.py report --output lab2/Отчёт_ЛР2_вариант_1.md\n'
        'python -m unittest discover -s lab2 -p "test_*.py" -v\n```\n',
        "Численные таблицы и контрпримеры этого файла получены функцией render_report(). "
        "В тестах операции сверяются с явно заданными таблицами, а результаты "
        "варианта 1 — с отдельным вычислителем на целочисленных значениях 0, 1, 2.\n",
    ]
    return "\n".join(out)
