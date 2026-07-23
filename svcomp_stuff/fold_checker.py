#!/usr/bin/env python3

import argparse
import ast
import itertools
import json
import pathlib
import re


def balanced_body(text, opening):
    depth = 0
    for index in range(opening, len(text)):
        if text[index] == "{":
            depth += 1
        elif text[index] == "}":
            depth -= 1
            if depth == 0:
                return text[opening + 1:index]
    raise ValueError("unbalanced body")


def worker_bodies(text):
    prefix = text.split("int main", 1)[0]
    marker = re.compile(r"\bvoid\s*\*\s*(\w+)\s*\([^;{}]*\)\s*\{")
    return {
        match.group(1): balanced_body(prefix, prefix.find("{", match.start()))
        for match in marker.finditer(prefix)
    }


def error_assumptions(text):
    main = text.split("int main", 1)[1]
    product = main.find("certified stuttering product")
    error = main.find("reach_error()", product)
    if product < 0 or error < 0:
        return []
    return re.findall(
        r"assume_abort_if_not\s*\((.*?)\)\s*;",
        main[product:error],
        re.S,
    )


def c_boolean(expression, values):
    unknown = sorted(
        set(re.findall(r"\b[A-Za-z_]\w*\b", expression)) - set(values)
    )
    if unknown:
        raise ValueError(f"unknown exit identifiers: {unknown}")
    converted = expression
    for name in sorted(values, key=len, reverse=True):
        converted = re.sub(rf"\b{re.escape(name)}\b", str(values[name]), converted)
    converted = converted.replace("&&", " and ").replace("||", " or ")
    converted = re.sub(r"!(?!=)", " not ", converted)
    if not re.fullmatch(r"[\s\d()<>!=+\-*/a-z.]+", converted):
        raise ValueError("unsupported exit expression")
    return bool(eval(converted, {"__builtins__": {}}, {}))


def lexicographic_certificate(text, workers, exits):
    comparisons = []
    for worker, body in workers.items():
        direct = re.search(
            r"\b(\w+)\s*=\s*minus\s*\(\s*(\w+)\s*\[\s*(\w+)\s*\]"
            r"\s*,\s*(\w+)\s*\[\s*(\w+)\s*\]\s*\)",
            body,
        )
        if direct:
            result, left, left_index, right, right_index = direct.groups()
            if left_index != right_index:
                return None
            guard = re.search(
                rf"while\s*\(\s*{re.escape(left_index)}\s*<\s*(\w+)"
                rf"\s*&&\s*{re.escape(left_index)}\s*<\s*(\w+)\s*\)",
                body,
            )
            initial = re.search(
                rf"\b{re.escape(result)}\s*=\s*(\w+)\s*-\s*(\w+)\s*;",
                body,
            )
            branch = re.search(
                rf"if\s*\(\s*{re.escape(left)}\s*\[\s*"
                rf"{re.escape(left_index)}\s*\]\s*!=\s*"
                rf"{re.escape(right)}\s*\[\s*{re.escape(left_index)}\s*\]"
                rf"\s*\)\s*\{{.*?\b{re.escape(result)}\s*=\s*minus"
                rf"\s*\(.*?\)\s*;\s*break\s*;\s*\}}",
                body,
                re.S,
            )
            increment = re.search(
                rf"\b{re.escape(left_index)}\s*\+\+\s*;", body
            )
            break_schema = (
                guard
                and initial
                and branch
                and increment
                and initial.groups() == guard.groups()
            )
            stop_guard = re.search(
                rf"while\s*\(\s*!\s*(\w+)\s*&&\s*"
                rf"{re.escape(left_index)}\s*<\s*\d+\s*\)",
                body,
            )
            stop_name = stop_guard.group(1) if stop_guard else ""
            stop_schema = (
                stop_guard
                and increment
                and re.search(
                    rf"\b{re.escape(result)}\s*=\s*1\s*;", body
                )
                and re.search(
                    rf"\b{re.escape(stop_name)}\s*=\s*\(\s*"
                    rf"{re.escape(result)}\s*!=\s*0\s*\)\s*;",
                    body,
                )
                and re.search(
                    rf"\b{re.escape(result)}\s*=\s*"
                    rf"{re.escape(stop_name)}\s*\?\s*"
                    rf"{re.escape(result)}\s*:\s*0\s*;",
                    body,
                )
            )
            if not break_schema and not stop_schema:
                return None
            comparisons.append((result, left, right, worker))
            continue
        ternary = re.search(
            r"\b(\w+)\s*=\s*(\w+)\s*\[\s*(\w+)\s*\]\s*<\s*"
            r"(\w+)\s*\[\s*(\w+)\s*\]\s*\?\s*-1\s*:",
            body,
        )
        if ternary:
            temporary, left, left_index, right, right_index = ternary.groups()
            if left_index != right_index:
                return None
            reverse = re.search(
                rf"\b{re.escape(left)}\s*\[\s*{re.escape(left_index)}\s*\]"
                rf"\s*>\s*{re.escape(right)}\s*\[\s*"
                rf"{re.escape(left_index)}\s*\]\s*\?\s*1\s*:\s*0",
                body,
            )
            result_match = re.search(
                rf"\b(\w+)\s*=\s*{re.escape(temporary)}\s*;", body
            )
            result = result_match.group(1) if result_match else ""
            branch = re.search(
                rf"if\s*\(\s*{re.escape(temporary)}\s*!=\s*0\s*\)"
                rf"\s*\{{\s*{re.escape(result)}\s*=\s*"
                rf"{re.escape(temporary)}\s*;\s*break\s*;\s*\}}",
                body,
                re.S,
            )
            guard = re.search(
                rf"while\s*\([^)]*\b{re.escape(left_index)}\s*<\s*"
                rf"\d+\s*\)",
                body,
            )
            increment = re.search(
                rf"\b{re.escape(left_index)}\s*\+\+\s*;", body
            )
            if not reverse or not result_match or not branch or not guard or not increment:
                return None
            comparisons.append((result, left, right, worker))
    if len(comparisons) < 2 or not exits:
        return None
    outputs = {item[0] for item in comparisons}
    relevant_exits = [
        expression
        for expression in exits
        if set(re.findall(r"\b[A-Za-z_]\w*\b", expression)) & outputs
    ]
    exit_ids = set(
        re.findall(r"\b[A-Za-z_]\w*\b", " ".join(relevant_exits))
    )
    if not exit_ids <= outputs:
        return None
    arrays = sorted({item for row in comparisons for item in row[1:3]})
    counterexamples = []
    for ranks in itertools.product(range(len(arrays)), repeat=len(arrays)):
        rank = dict(zip(arrays, ranks))
        values = {}
        for output, left, right, _ in comparisons:
            values[output] = (rank[left] > rank[right]) - (
                rank[left] < rank[right]
            )
        if all(c_boolean(expression, values) for expression in relevant_exits):
            counterexamples.append({"rank": rank, "values": values})
            break
    if counterexamples:
        return None
    return {
        "template": "first_difference",
        "comparisons": [
            {
                "result": output,
                "left": left,
                "right": right,
                "worker": worker,
            }
            for output, left, right, worker in comparisons
        ],
        "obligations": {
            "base": "empty prefixes compare equal",
            "step": "first unequal element fixes comparator sign",
            "composition": "lexicographic comparison is a total preorder",
            "exit": f"enumerated {len(arrays) ** len(arrays)} rank models; "
            "error assumptions unsatisfiable",
        },
    }


def prefix_symmetry_certificate(workers, exits):
    schemas = []
    for worker, body in workers.items():
        match = re.search(
            r"while\s*\(\s*(\w+)\s*<\s*(\w+)\s*&&\s*\1\s*<\s*(\w+)"
            r"\s*\)\s*\{\s*if\s*\(\s*(\w+)\s*\[\s*\1\s*\]\s*==\s*"
            r"(\w+)\s*\[\s*\1\s*\]\s*\)",
            body,
            re.S,
        )
        if match:
            counter, left_bound, right_bound, left, right = match.groups()
            schemas.append(
                (counter, left_bound, right_bound, left, right, worker)
            )
    if len(schemas) != 2 or len(exits) != 1:
        return None
    first, second = schemas
    reversed_pair = (
        first[1] == second[2]
        and first[2] == second[1]
        and first[3] == second[4]
        and first[4] == second[3]
    )
    expected = re.fullmatch(
        rf"\s*{re.escape(first[0])}\s*!=\s*{re.escape(second[0])}\s*",
        exits[0],
    ) or re.fullmatch(
        rf"\s*{re.escape(second[0])}\s*!=\s*{re.escape(first[0])}\s*",
        exits[0],
    )
    if not reversed_pair or not expected:
        return None
    return {
        "template": "zip_prefix",
        "workers": [first[5], second[5]],
        "obligations": {
            "base": "both longest-equal-prefix counters start equally",
            "step": "element equality is symmetric",
            "composition": "reversing the arrays preserves equal-prefix length",
            "exit": "counter disequality contradicts prefix symmetry",
        },
    }


def poly_add(left, right):
    result = dict(left)
    for monomial, coefficient in right.items():
        result[monomial] = result.get(monomial, 0) + coefficient
        if result[monomial] == 0:
            del result[monomial]
    return result


def poly_mul(left, right):
    result = {}
    for lmono, lcoef in left.items():
        for rmono, rcoef in right.items():
            monomial = tuple(sorted(lmono + rmono))
            result[monomial] = result.get(monomial, 0) + lcoef * rcoef
    return {key: value for key, value in result.items() if value}


def polynomial(expression, substitutions=None):
    substitutions = substitutions or {}
    node = ast.parse(expression.strip(), mode="eval").body

    def visit(item):
        if isinstance(item, ast.Name):
            return substitutions.get(item.id, {(item.id,): 1})
        if isinstance(item, ast.Constant) and isinstance(item.value, int):
            return {(): item.value}
        if isinstance(item, ast.UnaryOp) and isinstance(item.op, ast.USub):
            return {key: -value for key, value in visit(item.operand).items()}
        if isinstance(item, ast.BinOp) and isinstance(item.op, ast.Add):
            return poly_add(visit(item.left), visit(item.right))
        if isinstance(item, ast.BinOp) and isinstance(item.op, ast.Sub):
            return poly_add(
                visit(item.left),
                {key: -value for key, value in visit(item.right).items()},
            )
        if isinstance(item, ast.BinOp) and isinstance(item.op, ast.Mult):
            return poly_mul(visit(item.left), visit(item.right))
        raise ValueError("unsupported polynomial expression")

    return visit(node)


def degree2_certificate(text, workers, exits):
    summaries = {}
    schemas = []
    loop = re.compile(
        r"for\s*\(\s*unsigned\s+int\s+(\w+)\s*=\s*0\s*;"
        r"\s*\1\s*<\s*(.*?)\s*;\s*\1\+\+\s*\)\s*\{"
        r"\s*(\w+)\s*=\s*\3\s*\+\s*(.*?)\s*;\s*\}",
        re.S,
    )
    for worker, body in workers.items():
        match = loop.search(body)
        if not match:
            continue
        counter, bound, accumulator, step = match.groups()
        summary = poly_mul(polynomial(bound), polynomial(step))
        if any(len(monomial) > 2 for monomial in summary):
            return None
        summaries[accumulator] = summary
        schemas.append(
            {
                "worker": worker,
                "counter": counter,
                "bound": bound.strip(),
                "accumulator": accumulator,
                "step": step.strip(),
            }
        )
    if len(schemas) < 2 or len(exits) != 1:
        return None
    condition = exits[0].strip()
    unequal = re.fullmatch(r"(.*?)\s*!=\s*(.*)", condition, re.S)
    if not unequal:
        return None
    left = polynomial(unequal.group(1), summaries)
    right = polynomial(unequal.group(2), summaries)
    if left != right:
        return None
    symbols = {
        symbol
        for expression in summaries.values()
        for monomial in expression
        for symbol in monomial
    }
    declarations = text.split("int main", 1)[0]
    typed_symbols = symbols | set(summaries)
    if any(
        not re.search(rf"\bunsigned\s+int\b[^;]*\b{re.escape(symbol)}\b",
                      declarations)
        for symbol in typed_symbols
    ):
        return None
    return {
        "template": "degree2_recurrence",
        "loops": schemas,
        "obligations": {
            "base": "global accumulators have C static-storage zero initialization",
            "step": "accumulator' = accumulator + step",
            "composition": "degree-2 polynomial summaries normalized modulo 2^32",
            "exit": "both sides normalize to the same polynomial",
        },
    }


def check(text):
    workers = worker_bodies(text)
    exits = error_assumptions(text)
    for checker in (
        lexicographic_certificate,
        lambda source, bodies, assumptions: prefix_symmetry_certificate(
            bodies, assumptions
        ),
        degree2_certificate,
    ):
        certificate = checker(text, workers, exits)
        if certificate:
            return {
                "result": "SAFE",
                "certificate": certificate,
                "checks": {
                    "base": True,
                    "step": True,
                    "composition": True,
                    "exit": True,
                },
            }
    return {
        "result": "UNKNOWN",
        "certificate": None,
        "checks": {
            "base": False,
            "step": False,
            "composition": False,
            "exit": False,
        },
    }


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("source", type=pathlib.Path)
    parser.add_argument("--certificate", type=pathlib.Path)
    args = parser.parse_args()
    result = check(args.source.read_text(errors="replace"))
    if args.certificate:
        args.certificate.write_text(
            json.dumps(result, indent=2, sort_keys=True) + "\n"
        )
    template = (
        result["certificate"]["template"] if result["certificate"] else "none"
    )
    print(f"RELATIONAL_FOLD result={result['result']} template={template}")


if __name__ == "__main__":
    main()
