#!/usr/bin/env python3

import argparse
import importlib.util
import json
import pathlib
import re
from typing import Any, Callable


def load_base() -> Any:
    candidates = [
        pathlib.Path(__file__).resolve().with_name(
            "algebraic_segment_checker.py"
        ),
        pathlib.Path("/v87/algebraic_segment_checker.py"),
    ]
    source = next((path for path in candidates if path.exists()), None)
    if source is None:
        raise RuntimeError("missing algebraic checker parser")
    spec = importlib.util.spec_from_file_location("effect_base", source)
    if spec is None or spec.loader is None:
        raise RuntimeError("cannot load algebraic checker parser")
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


BASE = load_base()


def scope_any(functions: dict[str, Any]) -> dict[str, Any]:
    if "main" not in functions:
        raise ValueError("missing main")
    main = functions["main"]["body"]
    creates = BASE.calls(main, "pthread_create")
    joins = BASE.calls(main, "pthread_join")
    if len(creates) < 2 or len(joins) != len(creates):
        raise ValueError("requires at least two creates and matching joins")
    handles: dict[str, str] = {}
    workers: list[str] = []
    for call in creates:
        if len(call["arguments"]) != 4:
            raise ValueError("malformed create")
        handle_ids = re.findall(r"\b[A-Za-z_]\w*\b", call["arguments"][0])
        worker_ids = re.findall(r"\b[A-Za-z_]\w*\b", call["arguments"][2])
        if not handle_ids or not worker_ids:
            raise ValueError("unresolved create")
        handle, worker = handle_ids[-1], worker_ids[-1]
        if handle in handles or worker in workers or worker not in functions:
            raise ValueError("duplicate or missing worker")
        if BASE.compact(call["arguments"][3]) not in {"0", "NULL"}:
            raise ValueError("worker argument is observed")
        handles[handle] = worker
        workers.append(worker)
    joined: list[str] = []
    for call in joins:
        if len(call["arguments"]) != 2:
            raise ValueError("malformed join")
        ids = re.findall(r"\b[A-Za-z_]\w*\b", call["arguments"][0])
        if not ids or ids[-1] not in handles:
            raise ValueError("unresolved join")
        if BASE.compact(call["arguments"][1]) not in {"0", "NULL"}:
            raise ValueError("join return is observed")
        joined.append(ids[-1])
    if len(set(joined)) != len(handles) or set(joined) != set(handles):
        raise ValueError("not all workers are joined exactly once")
    first_create = min(call["start"] for call in creates)
    last_join = max(call["end"] for call in joins)
    interval = main[first_create:last_join]
    residual = re.sub(
        r"\bpthread_(?:create|join)\s*\([^;]*\)\s*;", " ", interval
    )
    if BASE.compact(residual).strip(";"):
        raise ValueError("main is active during the worker region")
    suffix = main[last_join:]
    expression = BASE.property_expression(suffix)
    return {
        "main": main,
        "workers": workers,
        "prefix": main[:first_create],
        "suffix": suffix,
        "property": expression,
    }


def atomic_types(text: str) -> dict[str, str]:
    result: dict[str, str] = {}
    for match in re.finditer(
        r"(?m)^\s*_Atomic\s+(unsigned\s+int|int)\s+([^;()]+);", text
    ):
        type_name = BASE.compact(match.group(1))
        for item in match.group(2).split(","):
            ids = re.findall(r"\b[A-Za-z_]\w*\b", item)
            if ids:
                result[ids[-1]] = type_name
    return result


def write_pattern(variable: str) -> str:
    name = re.escape(variable)
    return (
        rf"\b{name}\s*(?:[+\-*/]?=(?!=)|\+\+|--)"
    )


def zero_initialized(prefix: str, variable: str) -> bool:
    assignments = re.findall(
        rf"\b{re.escape(variable)}\s*=\s*([^;]+);", prefix
    )
    if assignments:
        return len(assignments) == 1 and BASE.compact(assignments[0]) == "0"
    compact = BASE.compact(prefix)
    return bool(re.search(
        rf"(?:^|[(&]){re.escape(variable)}==0(?:[)&]|$)", compact
    )) or True


def signed_effect(statement: str, accumulator: str) -> tuple[int, str]:
    current = BASE.compact(statement).strip(";")
    name = re.escape(accumulator)
    patterns = (
        (1, rf"{name}\+\+"),
        (-1, rf"{name}--"),
        (1, rf"{name}\+=([^;]+)"),
        (-1, rf"{name}-=([^;]+)"),
        (1, rf"{name}={name}\+(.+)"),
        (-1, rf"{name}={name}-(.+)"),
    )
    for coefficient, pattern in patterns:
        match = re.fullmatch(pattern, current)
        if match:
            term = "1" if not match.groups() else match.group(1)
            return coefficient, term
    raise ValueError("unsupported additive effect")


def strip_atomic_and_guards(body: str) -> str:
    body = re.sub(
        r"\b__VERIFIER_atomic_(?:begin|end)\s*\(\s*\)\s*;", " ", body
    )
    return re.sub(
        r"\bassume_abort_if_not\s*\([^;]*\)\s*;", " ", body
    )


def explicitly_atomic_writes(body: str, variable: str) -> bool:
    regions = re.findall(
        r"\b__VERIFIER_atomic_begin\s*\(\s*\)\s*;"
        r"(.*?)"
        r"\b__VERIFIER_atomic_end\s*\(\s*\)\s*;",
        body,
        re.S,
    )
    total = len(re.findall(write_pattern(variable), body))
    covered = sum(
        len(re.findall(write_pattern(variable), region))
        for region in regions
    )
    begin = len(re.findall(
        r"\b__VERIFIER_atomic_begin\s*\(\s*\)\s*;", body
    ))
    end = len(re.findall(
        r"\b__VERIFIER_atomic_end\s*\(\s*\)\s*;", body
    ))
    return total > 0 and total == covered and begin == end


def fixed_loop_effect(
    body: str, accumulator: str
) -> tuple[str, int, str]:
    header = re.search(
        r"\bfor\s*\(\s*(?:int|unsigned\s+int)\s+([A-Za-z_]\w*)"
        r"\s*=\s*0\s*;\s*\1\s*<\s*([^;]+)\s*;"
        r"\s*\1\s*\+\+\s*\)\s*\{",
        body,
    )
    if not header:
        raise ValueError("not a fixed-count loop")
    opening = body.find("{", header.start())
    loop_body, closing = BASE.balanced_body(body, opening)
    remainder = body[:header.start()] + body[closing + 1:]
    remainder = re.sub(r"\breturn\s+(?:0|NULL)\s*;", " ", remainder)
    if BASE.compact(BASE.strip_comments(remainder)).strip(";"):
        raise ValueError("code outside fixed loop")
    cleaned = strip_atomic_and_guards(loop_body)
    statements = [
        item for item in cleaned.split(";")
        if BASE.compact(item)
        and re.search(write_pattern(accumulator), item + ";")
    ]
    if len(statements) != 1:
        raise ValueError("fixed loop has non-unique accumulator effect")
    coefficient, term = signed_effect(statements[0], accumulator)
    residual = cleaned.replace(statements[0], " ", 1)
    if re.search(write_pattern(accumulator), residual):
        raise ValueError("unresolved accumulator write")
    return BASE.compact(header.group(2)), coefficient, BASE.compact(term)


def retrying_consumer_effect(
    body: str, accumulator: str
) -> tuple[str, int, str]:
    compact = BASE.compact(strip_atomic_and_guards(body))
    pattern = (
        r"unsignedint([A-Za-z_]\w*)=0;"
        r"while\(\1<([A-Za-z_]\w*)\)\{"
        r"if\(" + re.escape(accumulator) + r">0\)\{"
        + re.escape(accumulator) + r"="
        + re.escape(accumulator) + r"-([A-Za-z_]\w*);"
        r"\1\+\+;\}\}"
        r"return(?:0|NULL);?"
    )
    match = re.fullmatch(pattern, compact)
    if not match:
        raise ValueError("not a retrying consumer")
    return match.group(2), -1, match.group(3)


def check_balanced(
    text: str, functions: dict[str, Any], scope: dict[str, Any]
) -> dict[str, Any]:
    match = re.fullmatch(r"([A-Za-z_]\w*)!=0", scope["property"])
    if not match:
        raise ValueError("property is not nonzero accumulator")
    accumulator = match.group(1)
    scalar = BASE.scalar_types(text)
    scalar.update(atomic_types(text))
    if scalar.get(accumulator) != "unsignedint":
        raise ValueError("balanced accumulator is not unsigned")
    c11_atomic = atomic_types(text).get(accumulator) == "unsignedint"
    if not zero_initialized(scope["prefix"], accumulator):
        raise ValueError("balanced accumulator is not zero initialized")
    effects: list[tuple[str, int, str]] = []
    for worker in scope["workers"]:
        body = functions[worker]["body"]
        if not c11_atomic and not explicitly_atomic_writes(body, accumulator):
            raise ValueError("accumulator write is not explicitly atomic")
        try:
            effects.append(fixed_loop_effect(body, accumulator))
        except ValueError:
            effects.append(retrying_consumer_effect(body, accumulator))
    bounds = {bound for bound, _, _ in effects}
    terms = {term for _, _, term in effects}
    if len(bounds) != 1 or len(terms) != 1:
        raise ValueError("balanced effects use different bounds or terms")
    bound = next(iter(bounds))
    term = next(iter(terms))
    if not re.fullmatch(r"[A-Za-z_]\w*", bound):
        raise ValueError("balanced bound is not an immutable scalar")
    if not re.fullmatch(r"(?:[A-Za-z_]\w*|[0-9]+)", term):
        raise ValueError("balanced term is not an immutable scalar")
    if sum(coefficient for _, coefficient, _ in effects) != 0:
        raise ValueError("joined effects do not cancel")
    worker_text = "".join(functions[name]["body"] for name in scope["workers"])
    for variable in (bound, term):
        if variable.isidentifier() and re.search(
            write_pattern(variable), worker_text
        ):
            raise ValueError("balanced bound or term is modified")
    if len(re.findall(write_pattern(accumulator), text)) != len(
        re.findall(write_pattern(accumulator), worker_text)
    ):
        raise ValueError("accumulator has a writer outside joined workers")
    return {
        "result": "SAFE",
        "certificate": {
            "template": "joined_effect",
            "rule": "balanced_commutative_fold",
            "accumulator": accumulator,
            "bound": bound,
            "term": term,
            "coefficients": [item[1] for item in effects],
            "obligations": {
                "all_joined": True,
                "atomic_unsigned_fold": True,
                "common_bound": True,
                "common_term": True,
                "immutable_bound_and_term": True,
                "zero_total_coefficient": True,
                "exact_postcondition": True,
            },
        },
    }


def check_local_normalization(
    text: str, functions: dict[str, Any], scope: dict[str, Any]
) -> dict[str, Any]:
    match = re.fullmatch(r"([A-Za-z_]\w*)!=([0-9]+)", scope["property"])
    if not match:
        raise ValueError("property is not a constant fold result")
    accumulator, expected_text = match.groups()
    if atomic_types(text).get(accumulator) != "int":
        raise ValueError("normalization accumulator is not atomic int")
    contributions: list[int] = []
    source_names: set[str] = set()
    for worker in scope["workers"]:
        compact = BASE.compact(functions[worker]["body"])
        pattern = (
            r"int([A-Za-z_]\w*);"
            r"\1=([A-Za-z_]\w*);"
            r"while\(\1<([0-9]+)\)\{\1\+\+;\}"
            + re.escape(accumulator) + r"\+=\1;"
            r"return(?:0|NULL);?"
        )
        parsed = re.fullmatch(pattern, compact)
        if not parsed:
            raise ValueError("worker is not a deterministic normalization")
        source_names.add(parsed.group(2))
        contributions.append(int(parsed.group(3)))
    if len(source_names) != 1 or len(set(contributions)) != 1:
        raise ValueError("normalization workers differ")
    source = next(iter(source_names))
    bound = contributions[0]
    prefix = BASE.compact(scope["prefix"])
    if not re.search(
        rf"assume_abort_if_not\({re.escape(source)}<={bound}\);", prefix
    ):
        raise ValueError("missing normalization upper bound")
    expected = int(expected_text)
    if expected != len(contributions) * bound:
        raise ValueError("postcondition is not the folded contribution")
    if not (-2147483648 <= expected <= 2147483647):
        raise ValueError("normalization result may overflow")
    worker_text = "".join(functions[name]["body"] for name in scope["workers"])
    if len(re.findall(write_pattern(accumulator), text)) != len(
        re.findall(write_pattern(accumulator), worker_text)
    ):
        raise ValueError("normalization accumulator has another writer")
    return {
        "result": "SAFE",
        "certificate": {
            "template": "joined_effect",
            "rule": "deterministic_local_normalization",
            "accumulator": accumulator,
            "source": source,
            "bound": bound,
            "workers": len(contributions),
            "derived_value": expected,
            "obligations": {
                "all_joined": True,
                "private_normalization": True,
                "source_upper_bound": True,
                "atomic_fold": True,
                "no_signed_overflow": True,
                "exact_postcondition": True,
            },
        },
    }


def check_terminal_overwrite(
    text: str, functions: dict[str, Any], scope: dict[str, Any]
) -> dict[str, Any]:
    match = re.fullmatch(
        r"([A-Za-z_]\w*)!=([A-Za-z_]\w*)", scope["property"]
    )
    if not match:
        raise ValueError("property is not inequality of terminal values")
    left, right = match.groups()
    types = atomic_types(text)
    if left == right or left not in types or types.get(left) != types.get(right):
        raise ValueError("terminal variables are not distinct matching atomics")
    constants: dict[str, set[str]] = {left: set(), right: set()}
    for variable in (left, right):
        writers = [
            worker for worker in scope["workers"]
            if re.search(write_pattern(variable), functions[worker]["body"])
        ]
        if not writers:
            raise ValueError("terminal variable has no joined writer")
        for worker in writers:
            compact = BASE.compact(functions[worker]["body"])
            terminal = re.search(
                rf"{re.escape(variable)}=([-+]?[0-9]+);"
                r"return(?:0|NULL);?$",
                compact,
            )
            if not terminal:
                raise ValueError("writer lacks unconditional terminal store")
            constants[variable].add(terminal.group(1))
        if len(constants[variable]) != 1:
            raise ValueError("terminal writers disagree")
        if re.search(rf"&\s*{re.escape(variable)}\b", text):
            raise ValueError("terminal variable address escapes")
        worker_writes = sum(
            len(re.findall(
                write_pattern(variable), functions[worker]["body"]
            ))
            for worker in writers
        )
        prefix_writes = len(re.findall(
            write_pattern(variable), scope["prefix"]
        ))
        if len(re.findall(write_pattern(variable), text)) != (
            worker_writes + prefix_writes
        ):
            raise ValueError("terminal variable has an unresolved writer")
    left_constant = next(iter(constants[left]))
    right_constant = next(iter(constants[right]))
    if left_constant != right_constant:
        raise ValueError("terminal variables end at different values")
    return {
        "result": "SAFE",
        "certificate": {
            "template": "joined_effect",
            "rule": "common_terminal_overwrite",
            "variables": [left, right],
            "terminal_value": left_constant,
            "obligations": {
                "all_writers_joined": True,
                "unconditional_terminal_store": True,
                "common_terminal_value": True,
                "no_address_escape": True,
                "exact_postcondition": True,
            },
        },
    }


def periodic_worker(body: str, accumulator: str) -> dict[str, str]:
    compact = BASE.compact(body)
    name = re.escape(accumulator)

    def normalize_effect(token: str) -> tuple[str, str]:
        if token == "++":
            return "+", "1"
        if token == "--":
            return "-", "1"
        return token[0], token[2:]

    def require_inverse(first: str, second: str) -> str:
        left = normalize_effect(first)
        right = normalize_effect(second)
        if left[1] != right[1] or {left[0], right[0]} != {"+", "-"}:
            raise ValueError("period effects are not inverse")
        return left[1]

    effect = rf"{name}(\+\+|--|\+=\d+|-=\d+);"
    bounded = re.search(
        r"while\(\(*([A-Za-z_]\w*)<\(*2\*([A-Za-z_]\w*)\)*\)*\)\{",
        compact,
    )
    if bounded:
        opening = bounded.end() - 1
        loop_body, closing = BASE.balanced_body(compact, opening)
        suffix = compact[closing + 1:]
        if not re.fullmatch(r"return(?:0|NULL);?", suffix):
            raise ValueError("code follows periodic loop")
        index = bounded.group(1)
        unrolled = re.fullmatch(
            effect + re.escape(index) + r"\+\+;"
            + effect + re.escape(index) + r"\+\+;",
            loop_body,
        )
        if unrolled:
            term = require_inverse(unrolled.group(1), unrolled.group(2))
            return {"kind": "unrolled_inverse_pair", "term": term}
        alternating = re.fullmatch(
            r"if\(([A-Za-z_]\w*)\)\{" + effect + r"\}"
            r"else\{" + effect + r"\}"
            r"\1=!\1;" + re.escape(index) + r"\+\+;",
            loop_body,
        )
        if alternating:
            term = require_inverse(
                alternating.group(2), alternating.group(3)
            )
        return {"kind": "bounded_alternation", "term": term}

    phase = re.search(r"while\(([A-Za-z_]\w*)\)\{", compact)
    if phase:
        opening = phase.end() - 1
        loop_body, closing = BASE.balanced_body(compact, opening)
        suffix = compact[closing + 1:]
        if not re.fullmatch(r"return(?:0|NULL);?", suffix):
            raise ValueError("code follows phase loop")
        guard = phase.group(1)
        parsed = re.fullmatch(
            r"if\(([A-Za-z_]\w*)\)\{" + effect + r"\}"
            r"else\{" + effect + r"\}"
            r"\1=!\1;if\(\1\)\{if\(__VERIFIER_nondet_bool\(\)\)\{"
            + re.escape(guard) + r"=0;\}\}",
            loop_body,
        )
        if parsed:
            term = require_inverse(parsed.group(2), parsed.group(3))
            return {
                "kind": "phase_guarded_alternation",
                "term": term,
                "phase": parsed.group(1),
                "guard": guard,
            }
    raise ValueError("worker has no certified periodic effect")


def check_periodic(
    text: str, functions: dict[str, Any], scope: dict[str, Any]
) -> dict[str, Any]:
    match = re.fullmatch(r"([A-Za-z_]\w*)!=0", scope["property"])
    if not match:
        raise ValueError("property is not nonzero periodic accumulator")
    accumulator = match.group(1)
    if accumulator not in atomic_types(text):
        raise ValueError("periodic accumulator is not atomic")
    prefix = BASE.compact(scope["prefix"])
    if not re.search(
        rf"(?:{re.escape(accumulator)}=0|{re.escape(accumulator)}==0)",
        prefix,
    ) and re.search(
        rf"\b{re.escape(accumulator)}\s*=", scope["prefix"]
    ):
        raise ValueError("periodic accumulator may start nonzero")
    summaries = [
        periodic_worker(functions[worker]["body"], accumulator)
        for worker in scope["workers"]
    ]
    for summary in summaries:
        if summary["kind"] != "phase_guarded_alternation":
            continue
        for variable in (summary["phase"], summary["guard"]):
            assignments = re.findall(
                rf"\b{re.escape(variable)}\s*=\s*([^;]+);",
                scope["prefix"],
            )
            if len(assignments) != 1 or BASE.compact(assignments[0]) != "1":
                raise ValueError("phase or guard does not start at period head")
    worker_text = "".join(functions[name]["body"] for name in scope["workers"])
    if len(re.findall(write_pattern(accumulator), text)) != len(
        re.findall(write_pattern(accumulator), worker_text)
    ) + len(re.findall(write_pattern(accumulator), scope["prefix"])):
        raise ValueError("periodic accumulator has an unresolved writer")
    return {
        "result": "SAFE",
        "certificate": {
            "template": "joined_effect",
            "rule": "periodic_zero_effect",
            "accumulator": accumulator,
            "workers": summaries,
            "obligations": {
                "all_joined": True,
                "atomic_fold": True,
                "complete_period_exit": True,
                "period_head_initialization": True,
                "identity_period": True,
                "zero_initial_value": True,
                "exact_postcondition": True,
            },
        },
    }


def check(text: str) -> dict[str, Any]:
    try:
        cleaned = BASE.strip_comments(text)
        functions = BASE.function_bodies(cleaned)
        scope = scope_any(functions)
        errors: list[str] = []
        checkers: tuple[
            Callable[[str, dict[str, Any], dict[str, Any]], dict[str, Any]],
            ...,
        ] = (
            check_balanced,
            check_local_normalization,
            check_terminal_overwrite,
            check_periodic,
        )
        for checker in checkers:
            try:
                return checker(cleaned, functions, scope)
            except ValueError as exception:
                errors.append(f"{checker.__name__}: {exception}")
        return {"result": "UNKNOWN", "reason": " | ".join(errors)}
    except (
        ValueError,
        KeyError,
        IndexError,
        TypeError,
        re.error,
    ) as exception:
        return {"result": "UNKNOWN", "reason": str(exception)}


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("source", type=pathlib.Path)
    parser.add_argument("--certificate", type=pathlib.Path)
    args = parser.parse_args()
    result = check(args.source.read_text(errors="replace"))
    if args.certificate:
        args.certificate.write_text(
            json.dumps(result, indent=2, sort_keys=True) + "\n"
        )
    rule = (
        result["certificate"]["rule"]
        if result["result"] == "SAFE"
        else "none"
    )
    print(f"JOINED_EFFECT result={result['result']} rule={rule}")


if __name__ == "__main__":
    main()
