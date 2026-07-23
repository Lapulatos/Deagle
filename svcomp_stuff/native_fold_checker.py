#!/usr/bin/env python3

import argparse
import importlib.util
import json
import pathlib
import re


def load_fold_checker():
    candidates = [
        pathlib.Path(__file__).resolve().with_name("fold_checker.py"),
        pathlib.Path("/v80/fold_checker.py"),
        pathlib.Path(__file__).resolve().parents[1]
        / "relational-fold-checker-v80-20260723"
        / "fold_checker.py",
    ]
    source = next((path for path in candidates if path.exists()), None)
    if source is None:
        raise RuntimeError("missing V80 fold checker")
    spec = importlib.util.spec_from_file_location("v80_fold_checker", source)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


FOLD = load_fold_checker()


def strip_comments(text):
    text = re.sub(r"/\*.*?\*/", " ", text, flags=re.S)
    return re.sub(r"//[^\n]*", " ", text)


def main_body(text):
    match = re.search(r"\bint\s+main\s*\([^;{}]*\)\s*\{", text)
    if not match:
        raise ValueError("missing main")
    opening = text.find("{", match.start())
    return FOLD.balanced_body(text, opening)


def calls(body, name):
    pattern = re.compile(rf"\b{re.escape(name)}\s*\(([^;]*)\)\s*;")
    return [
        {
            "start": match.start(),
            "end": match.end(),
            "arguments": [part.strip() for part in match.group(1).split(",")],
            "text": match.group(0),
        }
        for match in pattern.finditer(body)
    ]


def local_names(body):
    names = {"_argptr"}
    declaration = re.compile(
        r"\b(?:_Bool|bool|char|short|int|long|unsigned|signed|size_t|"
        r"void\s*\*)\b([^;{}()]*)\s*;"
    )
    for match in declaration.finditer(body):
        for part in match.group(1).split(","):
            identifiers = [
                name
                for name in re.findall(r"\b[A-Za-z_]\w*\b", part)
                if name
                not in {
                    "_Bool",
                    "bool",
                    "char",
                    "const",
                    "false",
                    "int",
                    "long",
                    "short",
                    "signed",
                    "size_t",
                    "static",
                    "true",
                    "unsigned",
                    "void",
                    "volatile",
                }
            ]
            if identifiers:
                names.add(identifiers[0])
    return names


def effect_summary(worker, body, all_functions):
    if re.search(r"\b(?:reach_error|__assert_fail|assert)\s*\(", body):
        raise ValueError(f"{worker}: worker assertion")
    if re.search(
        r"(?:\*\s*\w+|\w+\s*\[[^\]]+\])\s*"
        r"(?:[+\-*/]?=(?!=)|\+\+|--)",
        body,
    ):
        raise ValueError(f"{worker}: pointer or array write")
    locals_found = local_names(body)
    writes = set(
        re.findall(r"\b([A-Za-z_]\w*)\s*(?:[+\-*/]?=|\+\+|--)", body)
    ) - locals_found
    identifiers = set(re.findall(r"\b[A-Za-z_]\w*\b", body)) - locals_found
    calls_found = set(re.findall(r"\b([A-Za-z_]\w*)\s*\(", body))
    controls = {"if", "while", "for", "sizeof"}
    pure_builtins = {"assume_abort_if_not", "abort"}
    for callee in calls_found - controls - pure_builtins:
        helper = all_functions.get(callee)
        if helper is None:
            raise ValueError(f"{worker}: unresolved helper {callee}")
        helper_locals = local_names(helper)
        helper_writes = set(
            re.findall(
                r"\b([A-Za-z_]\w*)\s*(?:[+\-*/]?=|\+\+|--)", helper
            )
        ) - helper_locals
        helper_calls = set(
            re.findall(r"\b([A-Za-z_]\w*)\s*\(", helper)
        ) - controls - pure_builtins
        if helper_writes or helper_calls:
            raise ValueError(f"{worker}: impure helper {callee}")
    return {"writes": writes, "identifiers": identifiers}


def all_function_bodies(text):
    marker = re.compile(
        r"\b(?:void\s*\*?|int|unsigned\s+int|_Bool)\s+"
        r"([A-Za-z_]\w*)\s*\([^;{}]*\)\s*\{"
    )
    return {
        match.group(1): FOLD.balanced_body(
            text, text.find("{", match.start())
        )
        for match in marker.finditer(text)
    }


def concurrency_certificate(text):
    body = main_body(text)
    creates = calls(body, "pthread_create")
    joins = calls(body, "pthread_join")
    if len(creates) < 2 or len(creates) != len(joins):
        return None
    workers = {}
    handles = {}
    for call in creates:
        if len(call["arguments"]) != 4:
            return None
        handle_ids = re.findall(r"\b[A-Za-z_]\w*\b", call["arguments"][0])
        worker_ids = re.findall(r"\b[A-Za-z_]\w*\b", call["arguments"][2])
        if not handle_ids or not worker_ids:
            return None
        handle = handle_ids[-1]
        worker = worker_ids[-1]
        if handle in handles or worker in workers:
            return None
        handles[handle] = worker
        workers[worker] = handle
    joined = []
    for call in joins:
        if len(call["arguments"]) != 2:
            return None
        handle_ids = re.findall(r"\b[A-Za-z_]\w*\b", call["arguments"][0])
        if not handle_ids or handle_ids[-1] not in handles:
            return None
        if re.sub(r"\s+", "", call["arguments"][1]) not in {"0", "NULL"}:
            return None
        joined.append(handle_ids[-1])
    if set(joined) != set(handles) or len(joined) != len(set(joined)):
        return None
    first = min(call["start"] for call in creates)
    last = max(call["end"] for call in joins)
    concurrent = body[first:last]
    concurrent = re.sub(
        r"\bpthread_(?:create|join)\s*\([^;]*\)\s*;", " ", concurrent
    )
    if re.sub(r"[\s;]", "", strip_comments(concurrent)):
        return None
    if body.find("reach_error()", last) < 0:
        return None

    functions = all_function_bodies(text)
    if not set(workers) <= set(functions):
        return None
    effects = {}
    try:
        for worker in workers:
            effects[worker] = effect_summary(
                worker, functions[worker], functions
            )
    except ValueError:
        return None
    names = sorted(workers)
    for index, left in enumerate(names):
        for right in names[index + 1:]:
            if effects[left]["writes"] & effects[right]["writes"]:
                return None
            if effects[left]["writes"] & effects[right]["identifiers"]:
                return None
            if effects[right]["writes"] & effects[left]["identifiers"]:
                return None
    return {
        "workers": names,
        "handles": handles,
        "join_order": joined,
        "effects": {
            worker: {
                "writes": sorted(summary["writes"]),
            }
            for worker, summary in effects.items()
        },
        "obligations": {
            "all_joined": True,
            "main_idle": True,
            "resolved_helpers": True,
            "pairwise_independent": True,
            "property_after_joins": True,
        },
        "last_join_offset": last,
    }


def check(text):
    concurrency = concurrency_certificate(text)
    if concurrency is None:
        return {"result": "UNKNOWN", "concurrency": None, "fold": None}
    body = main_body(text)
    marker = concurrency["last_join_offset"]
    instrumented_body = (
        body[:marker]
        + "\n/* certified stuttering product */\n"
        + body[marker:]
    )
    main_match = re.search(r"\bint\s+main\s*\([^;{}]*\)\s*\{", text)
    opening = text.find("{", main_match.start())
    closing = opening + 1 + len(main_body(text))
    instrumented = (
        text[:opening + 1] + instrumented_body + text[closing:]
    )
    fold = FOLD.check(instrumented)
    if fold["result"] != "SAFE":
        return {"result": "UNKNOWN", "concurrency": concurrency, "fold": fold}
    concurrency.pop("last_join_offset", None)
    return {"result": "SAFE", "concurrency": concurrency, "fold": fold}


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
    fold_template = (
        result["fold"]["certificate"]["template"]
        if result["result"] == "SAFE"
        else "none"
    )
    print(
        f"NATIVE_RELATIONAL_FOLD result={result['result']} "
        f"template={fold_template}"
    )


if __name__ == "__main__":
    main()
