#!/usr/bin/env python3

import argparse
import json
import pathlib
import re


def strip_comments(text):
    text = re.sub(r"/\*.*?\*/", " ", text, flags=re.S)
    return re.sub(r"//[^\n]*", " ", text)


def compact(text):
    return re.sub(r"\s+", "", text)


def balanced_body(text, opening):
    depth = 0
    for index in range(opening, len(text)):
        if text[index] == "{":
            depth += 1
        elif text[index] == "}":
            depth -= 1
            if depth == 0:
                return text[opening + 1:index], index
    raise ValueError("unbalanced body")


def function_bodies(text):
    marker = re.compile(
        r"\b(?:void\s*\*?|int|unsigned\s+int|_Bool)\s+"
        r"([A-Za-z_]\w*)\s*\([^;{}]*\)\s*\{"
    )
    result = {}
    for match in marker.finditer(text):
        opening = text.find("{", match.start())
        body, closing = balanced_body(text, opening)
        result[match.group(1)] = {
            "body": body,
            "start": match.start(),
            "opening": opening,
            "closing": closing,
        }
    return result


def calls(body, name):
    pattern = re.compile(rf"\b{re.escape(name)}\s*\(([^;]*)\)\s*;")
    return [
        {
            "start": match.start(),
            "end": match.end(),
            "arguments": [part.strip() for part in match.group(1).split(",")],
        }
        for match in pattern.finditer(body)
    ]


def concurrency_scope(text, functions):
    if "main" not in functions:
        raise ValueError("missing main")
    main = functions["main"]["body"]
    creates = calls(main, "pthread_create")
    joins = calls(main, "pthread_join")
    if len(creates) != 3 or len(joins) != 3:
        raise ValueError("requires exactly three creates and joins")
    handles = {}
    workers = []
    for call in creates:
        if len(call["arguments"]) != 4:
            raise ValueError("malformed create")
        handle_ids = re.findall(r"\b[A-Za-z_]\w*\b", call["arguments"][0])
        worker_ids = re.findall(r"\b[A-Za-z_]\w*\b", call["arguments"][2])
        if not handle_ids or not worker_ids:
            raise ValueError("unresolved create")
        handle = handle_ids[-1]
        worker = worker_ids[-1]
        if handle in handles or worker in workers or worker not in functions:
            raise ValueError("duplicate or missing worker")
        handles[handle] = worker
        workers.append(worker)
    joined = []
    for call in joins:
        if len(call["arguments"]) != 2:
            raise ValueError("malformed join")
        handle_ids = re.findall(r"\b[A-Za-z_]\w*\b", call["arguments"][0])
        if not handle_ids or handle_ids[-1] not in handles:
            raise ValueError("unresolved join")
        if compact(call["arguments"][1]) not in {"0", "NULL"}:
            raise ValueError("join return value used")
        joined.append(handle_ids[-1])
    if set(joined) != set(handles) or len(set(joined)) != 3:
        raise ValueError("not all workers joined exactly once")
    first_create = min(call["start"] for call in creates)
    last_join = max(call["end"] for call in joins)
    interval = main[first_create:last_join]
    interval = re.sub(
        r"\bpthread_(?:create|join)\s*\([^;]*\)\s*;", " ", interval
    )
    if compact(interval).strip(";"):
        raise ValueError("main is active during worker interval")
    suffix = main[last_join:]
    if not re.search(
        r"assume_abort_if_not\s*\(.*\)\s*;\s*reach_error\s*\(\s*\)\s*;",
        suffix,
        re.S,
    ):
        raise ValueError("property is not after all joins")
    return {
        "main": main,
        "workers": workers,
        "first_create": first_create,
        "last_join": last_join,
        "suffix": suffix,
    }


def normalize_element(expression, index):
    expression = re.sub(rf"\b{re.escape(index)}\b", "$i", expression)
    return compact(expression)


def parse_update(body, index):
    body = strip_comments(body)
    atomic_begin = len(
        re.findall(r"\b__VERIFIER_atomic_begin\s*\(\s*\)\s*;", body)
    )
    atomic_end = len(
        re.findall(r"\b__VERIFIER_atomic_end\s*\(\s*\)\s*;", body)
    )
    if atomic_begin != atomic_end or atomic_begin > 1:
        raise ValueError("unmatched or nested atomic update")
    atomic = atomic_begin == 1
    body = re.sub(
        r"\b__VERIFIER_atomic_(?:begin|end)\s*\(\s*\)\s*;", " ", body
    )
    body_c = compact(body).strip(";")

    assignment = re.fullmatch(
        r"([A-Za-z_]\w*)=(?:\1\+(.+)|plus\(\1,(.+)\))",
        body_c,
    )
    if assignment:
        element = assignment.group(2) or assignment.group(3)
        style = "raw_add" if assignment.group(2) is not None else "guarded_add"
        return {
            "operator": "add",
            "style": style,
            "accumulator": assignment.group(1),
            "element": normalize_element(element, index),
            "atomic": atomic,
        }

    ordered = re.fullmatch(
        r"if\(([A-Za-z_]\w*)([<>])(.+)\)"
        r"\{\1=(.+);\}",
        body_c,
    )
    if ordered:
        compared = normalize_element(ordered.group(3), index)
        assigned = normalize_element(ordered.group(4), index)
        if compared != assigned:
            raise ValueError("ordered update assigns a different element")
        return {
            "operator": "max" if ordered.group(2) == "<" else "min",
            "style": "ordered",
            "accumulator": ordered.group(1),
            "element": compared,
            "atomic": atomic,
        }
    raise ValueError("unsupported loop update")


def parse_worker(worker, body):
    header = re.search(
        r"\bfor\s*\(\s*(?:int|unsigned\s+int)\s+([A-Za-z_]\w*)"
        r"\s*=\s*([^;]+)\s*;\s*\1\s*<\s*([^;]+)\s*;"
        r"\s*\1\s*\+\+\s*\)\s*\{",
        body,
    )
    if not header:
        raise ValueError(f"{worker}: unsupported loop header")
    opening = body.find("{", header.start())
    loop_body, closing = balanced_body(body, opening)
    remainder = body[:header.start()] + body[closing + 1:]
    remainder = re.sub(r"\breturn\s+(?:0|NULL)\s*;", " ", remainder)
    if compact(strip_comments(remainder)).strip(";"):
        raise ValueError(f"{worker}: code outside certified loop")
    update = parse_update(loop_body, header.group(1))
    update.update(
        {
            "worker": worker,
            "index": header.group(1),
            "start": compact(header.group(2)),
            "bound": compact(header.group(3)),
        }
    )
    return update


def scalar_types(text):
    types = {}
    for match in re.finditer(
        r"(?m)^\s*(unsigned\s+int|int)\s+([^;()]+)\s*;", text
    ):
        type_name = compact(match.group(1))
        for item in match.group(2).split(","):
            item = item.strip()
            if "=" in item or "[" in item or "*" in item:
                continue
            ids = re.findall(r"\b[A-Za-z_]\w*\b", item)
            if ids:
                types[ids[-1]] = type_name
    return types


def range_partition(updates, main_prefix):
    whole = [
        update for update in updates
        if update["start"] == "0" and update["bound"] == "N"
    ]
    prefix = [
        update for update in updates
        if update["start"] == "0" and update["bound"] == "M"
    ]
    suffix = [
        update for update in updates
        if update["start"] == "M" and update["bound"] == "N"
    ]
    if len(whole) != 1 or len(prefix) != 1 or len(suffix) != 1:
        raise ValueError("ranges are not exact whole/prefix/suffix")
    if not re.search(
        r"\bM\s*>=\s*0\s*&&\s*M\s*<=?\s*N\b", main_prefix
    ):
        raise ValueError("missing segment-bound assumption")
    return whole[0], prefix[0], suffix[0]


def helper_is_guarded_plus(functions):
    helper = functions.get("plus")
    if helper is None:
        return False
    body = compact(strip_comments(helper["body"]))
    return (
        body.count("assume_abort_if_not(") >= 2
        and "returna+b;" in body
    )


def property_expression(suffix):
    matches = list(
        re.finditer(r"assume_abort_if_not\s*\((.*?)\)\s*;", suffix, re.S)
    )
    if not matches:
        raise ValueError("missing postcondition")
    tail = suffix[matches[-1].end():]
    if not re.match(r"\s*reach_error\s*\(\s*\)\s*;", tail):
        raise ValueError("postcondition is not immediately asserted")
    return compact(matches[-1].group(1))


def expected_property(operator, whole, prefix, suffix, shared):
    w = re.escape(whole)
    p = re.escape(prefix)
    s = re.escape(suffix)
    if shared:
        return [rf"{w}!={p}"]
    if operator == "add":
        return [
            rf"{w}!={p}\+{s}",
            rf"{w}!={s}\+{p}",
            rf"{w}!=plus\({p},{s}\)",
            rf"{w}!=plus\({s},{p}\)",
        ]
    comparator = "<" if operator == "max" else ">"
    return [
        rf"{w}!=\({p}{comparator}{s}\?{s}:{p}\)",
        rf"{w}!=\({s}{comparator}{p}\?{p}:{s}\)",
    ]


def check(text):
    try:
        text = strip_comments(text)
        functions = function_bodies(text)
        scope = concurrency_scope(text, functions)
        updates = [
            parse_worker(worker, functions[worker]["body"])
            for worker in scope["workers"]
        ]
        operators = {update["operator"] for update in updates}
        elements = {update["element"] for update in updates}
        styles = {update["style"] for update in updates}
        if len(operators) != 1 or len(elements) != 1 or len(styles) != 1:
            raise ValueError("workers use different fold operations")
        operator = next(iter(operators))
        style = next(iter(styles))
        main_prefix = scope["main"][:scope["first_create"]]
        whole, prefix, suffix = range_partition(updates, main_prefix)
        accumulators = [
            whole["accumulator"],
            prefix["accumulator"],
            suffix["accumulator"],
        ]
        shared = (
            prefix["accumulator"] == suffix["accumulator"]
            and whole["accumulator"] != prefix["accumulator"]
        )
        independent = len(set(accumulators)) == 3
        if not (shared or independent):
            raise ValueError("unsupported accumulator sharing")
        if shared and not (prefix["atomic"] and suffix["atomic"]):
            raise ValueError("shared reduction is not atomic")
        if operator in {"max", "min"} and shared and not whole["atomic"]:
            raise ValueError("ordered shared comparison requires atomic loops")
        types = scalar_types(text)
        if any(accumulator not in types for accumulator in accumulators):
            raise ValueError("unresolved accumulator type")
        if len({types[accumulator] for accumulator in accumulators}) != 1:
            raise ValueError("incompatible accumulator types")
        if style == "raw_add" and types[whole["accumulator"]] != "unsignedint":
            raise ValueError("raw addition is not unsigned modular arithmetic")
        if style == "guarded_add" and not helper_is_guarded_plus(functions):
            raise ValueError("unresolved signed addition semantics")
        for accumulator in set(accumulators):
            if re.search(
                rf"\b{re.escape(accumulator)}\s*(?:[+\-*/]?=(?!=)|\+\+|--)",
                main_prefix,
            ):
                raise ValueError("accumulator is initialized in main")
        if re.search(
            r"\b[A-Za-z_]\w*\s*\[[^\]]+\]\s*"
            r"(?:[+\-*/]?=(?!=)|\+\+|--)",
            "".join(functions[worker]["body"] for worker in scope["workers"]),
        ):
            raise ValueError("worker writes an input array")
        expression = property_expression(scope["suffix"])
        patterns = expected_property(
            operator,
            whole["accumulator"],
            prefix["accumulator"],
            suffix["accumulator"],
            shared,
        )
        if not any(re.fullmatch(pattern, expression) for pattern in patterns):
            raise ValueError("postcondition is not the fold theorem")
        return {
            "result": "SAFE",
            "certificate": {
                "template": "atomic_shared_segment_fold"
                if shared
                else "independent_segment_fold",
                "operator": operator,
                "style": style,
                "element": whole["element"],
                "type": types[whole["accumulator"]],
                "whole": whole,
                "prefix": prefix,
                "suffix": suffix,
                "obligations": {
                    "all_joined": True,
                    "exact_partition": True,
                    "same_element": True,
                    "input_arrays_immutable": True,
                    "operator_semantics_checked": True,
                    "shared_updates_atomic": not shared
                    or (prefix["atomic"] and suffix["atomic"]),
                    "zero_global_initialization": True,
                    "exact_exit_formula": True,
                },
            },
        }
    except (ValueError, KeyError, IndexError, TypeError) as exception:
        return {"result": "UNKNOWN", "reason": str(exception)}


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
        result["certificate"]["template"]
        if result["result"] == "SAFE"
        else "none"
    )
    print(
        f"ALGEBRAIC_SEGMENT result={result['result']} "
        f"template={template}"
    )


if __name__ == "__main__":
    main()
