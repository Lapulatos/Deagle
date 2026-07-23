#!/usr/bin/env python3

import argparse
import importlib.util
import json
import pathlib
import re


def load_composite():
    candidates = [
        pathlib.Path(__file__).resolve().with_name(
            "composite_summary_checker.py"
        ),
        pathlib.Path("/v92/composite_summary_checker.py"),
    ]
    source = next((path for path in candidates if path.exists()), None)
    if source is None:
        raise RuntimeError("missing composite summary checker")
    spec = importlib.util.spec_from_file_location(
        "composite_summary_checker", source
    )
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


COMPOSITE = load_composite()
BASE = COMPOSITE.BASE


def four_worker_scope(text, functions):
    if "main" not in functions:
        raise ValueError("missing main")
    main = functions["main"]["body"]
    creates = BASE.calls(main, "pthread_create")
    joins = BASE.calls(main, "pthread_join")
    if len(creates) != 4 or len(joins) != 4:
        raise ValueError("requires exactly four creates and joins")
    handles = {}
    workers = []
    for call in creates:
        if len(call["arguments"]) != 4:
            raise ValueError("malformed create")
        handle_ids = re.findall(
            r"\b[A-Za-z_]\w*\b", call["arguments"][0]
        )
        worker_ids = re.findall(
            r"\b[A-Za-z_]\w*\b", call["arguments"][2]
        )
        if not handle_ids or not worker_ids:
            raise ValueError("unresolved create")
        handle, worker = handle_ids[-1], worker_ids[-1]
        if handle in handles or worker in workers or worker not in functions:
            raise ValueError("duplicate or missing worker")
        handles[handle] = worker
        workers.append(worker)
    joined = []
    for call in joins:
        if len(call["arguments"]) != 2:
            raise ValueError("malformed join")
        ids = re.findall(r"\b[A-Za-z_]\w*\b", call["arguments"][0])
        if not ids or ids[-1] not in handles:
            raise ValueError("unresolved join")
        if BASE.compact(call["arguments"][1]) not in {"0", "NULL"}:
            raise ValueError("join return value used")
        joined.append(ids[-1])
    if set(joined) != set(handles) or len(set(joined)) != 4:
        raise ValueError("not all workers joined exactly once")
    first_create = min(call["start"] for call in creates)
    last_join = max(call["end"] for call in joins)
    interval = main[first_create:last_join]
    interval = re.sub(
        r"\bpthread_(?:create|join)\s*\([^;]*\)\s*;", " ", interval
    )
    if BASE.compact(interval).strip(";"):
        raise ValueError("main is active during worker interval")
    suffix = main[last_join:]
    if not re.search(
        r"assume_abort_if_not\s*\(.*\)\s*;\s*"
        r"reach_error\s*\(\s*\)\s*;",
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


def atomic_blocks(text):
    pattern = re.compile(
        r"\b__VERIFIER_atomic_begin\s*\(\s*\)\s*;"
        r"(.*?)"
        r"\b__VERIFIER_atomic_end\s*\(\s*\)\s*;",
        re.S,
    )
    matches = list(pattern.finditer(text))
    residual = pattern.sub(" ", text)
    if BASE.compact(residual).strip(";"):
        raise ValueError("worker action outside atomic blocks")
    return [match.group(1) for match in matches]


def worker_loop(worker, body):
    loop = re.search(
        r"\bwhile\s*\(\s*([A-Za-z_]\w*)\s*\)\s*\{", body
    )
    if not loop:
        raise ValueError(f"{worker}: missing simple while loop")
    opening = body.find("{", loop.start())
    loop_body, closing = BASE.balanced_body(body, opening)
    prefix = body[:loop.start()]
    suffix = body[closing + 1:]
    suffix = re.sub(r"\breturn\s+(?:0|NULL)\s*;", " ", suffix)
    if BASE.compact(BASE.strip_comments(suffix)).strip(";"):
        raise ValueError(f"{worker}: code after loop")
    initial = atomic_blocks(prefix)
    if len(initial) != 1:
        raise ValueError(f"{worker}: unsupported initial guard")
    declaration = re.fullmatch(
        r"\s*_Bool\s+([A-Za-z_]\w*)\s*=\s*(.*?)\s*;\s*",
        initial[0],
        re.S,
    )
    if not declaration or declaration.group(1) != loop.group(1):
        raise ValueError(f"{worker}: unresolved loop guard")
    blocks = atomic_blocks(loop_body)
    if len(blocks) < 2:
        raise ValueError(f"{worker}: incomplete atomic loop")
    update = re.fullmatch(
        rf"\s*{re.escape(loop.group(1))}\s*=\s*(.*?)\s*;\s*",
        blocks[-1],
        re.S,
    )
    if not update:
        raise ValueError(f"{worker}: guard update is not last")
    initial_guard = BASE.compact(declaration.group(2))
    updated_guard = BASE.compact(update.group(1))
    if initial_guard != updated_guard:
        raise ValueError(f"{worker}: inconsistent loop guard")
    return {
        "worker": worker,
        "guard": initial_guard,
        "blocks": blocks[:-1],
    }


def assume_expressions(block):
    return [
        BASE.compact(match.group(1))
        for match in re.finditer(
            r"\bassume_abort_if_not\s*\(([^;]*)\)\s*;", block
        )
    ]


def allowed_action_block(block, assignments, increments):
    residual = re.sub(
        r"\bassume_abort_if_not\s*\([^;]*\)\s*;", " ", block
    )
    for assignment in assignments:
        residual = re.sub(assignment, " ", residual, count=1)
    for variable in increments:
        residual = re.sub(
            rf"\b{re.escape(variable)}\s*\+\+\s*;",
            " ",
            residual,
            count=1,
        )
    return not BASE.compact(residual).strip(";")


def equality_term(expressions):
    terms = []
    for expression in expressions:
        for term in expression.split("&&"):
            match = re.fullmatch(
                r"([A-Za-z_]\w*)\[([A-Za-z_]\w*)\]==(.+)",
                term,
            )
            if match:
                terms.append(match.groups())
    if len(terms) != 1:
        raise ValueError("producer has no unique queue-value constraint")
    return terms[0]


def parse_producer(loop):
    increment_occurrences = []
    equalities = []
    for index, block in enumerate(loop["blocks"]):
        for match in re.finditer(r"\b([A-Za-z_]\w*)\s*\+\+\s*;", block):
            increment_occurrences.append(
                (match.group(1), index, match.start())
            )
        expressions = assume_expressions(block)
        try:
            queue, back, element = equality_term(expressions)
            equalities.append((queue, back, element, index, block))
        except ValueError:
            pass
    if len(equalities) != 1 or len(increment_occurrences) != 2:
        raise ValueError("not a two-counter stream producer")
    queue, back, element, commit_index, commit_block = equalities[0]
    back_increments = [
        item for item in increment_occurrences if item[0] == back
    ]
    other = [
        item for item in increment_occurrences if item[0] != back
    ]
    if len(back_increments) != 1 or len(other) != 1:
        raise ValueError("producer counter roles are ambiguous")
    progress, progress_index, progress_position = other[0]
    back_index, back_position = (
        back_increments[0][1],
        back_increments[0][2],
    )
    if commit_index != back_index:
        raise ValueError("queue constraint and commit are not atomic")
    if back_index > progress_index or (
        back_index == progress_index and back_position > progress_position
    ):
        raise ValueError("progress is published before queue commit")
    expected_guard = f"{progress}<N"
    if loop["guard"] != expected_guard:
        raise ValueError("producer does not use common bound N")
    for block in loop["blocks"]:
        increments = [
            match.group(1)
            for match in re.finditer(
                r"\b([A-Za-z_]\w*)\s*\+\+\s*;", block
            )
        ]
        if not allowed_action_block(block, [], increments):
            raise ValueError("unsupported producer side effect")
    return {
        "role": "producer",
        "worker": loop["worker"],
        "queue": queue,
        "back": back,
        "progress": progress,
        "element": BASE.compact(element),
        "body": "".join(loop["blocks"]),
        "commit_before_progress": True,
    }


def parse_consumer(loop):
    parsed = re.fullmatch(
        r"([A-Za-z_]\w*)<N\|\|"
        r"([A-Za-z_]\w*)<([A-Za-z_]\w*)",
        loop["guard"],
    )
    if not parsed:
        raise ValueError("consumer guard does not publish-and-drain")
    progress, front, back = parsed.groups()
    consume = []
    for index, block in enumerate(loop["blocks"]):
        assignment = re.search(
            r"\b([A-Za-z_]\w*)\s*=\s*plus\s*\(\s*\1\s*,\s*"
            r"([A-Za-z_]\w*)\s*\[\s*"
            + re.escape(front)
            + r"\s*\]\s*\)\s*;",
            block,
        )
        if assignment:
            consume.append((index, block, assignment))
    if len(consume) != 1:
        raise ValueError("consumer has no unique fold")
    _, block, assignment = consume[0]
    accumulator, queue = assignment.group(1), assignment.group(2)
    if len(re.findall(
        rf"\b{re.escape(front)}\s*\+\+\s*;", block
    )) != 1:
        raise ValueError("consumer does not advance front atomically")
    assumptions = assume_expressions(block)
    if not any(
        re.search(
            rf"(?:^|&&){re.escape(front)}<{re.escape(back)}(?:&&|$)",
            expression,
        )
        for expression in assumptions
    ):
        raise ValueError("consumer does not require committed data")
    assignment_pattern = (
        rf"\b{re.escape(accumulator)}\s*=\s*plus\s*\(\s*"
        rf"{re.escape(accumulator)}\s*,\s*{re.escape(queue)}\s*"
        rf"\[\s*{re.escape(front)}\s*\]\s*\)\s*;"
    )
    for current in loop["blocks"]:
        increments = [
            match.group(1)
            for match in re.finditer(
                r"\b([A-Za-z_]\w*)\s*\+\+\s*;", current
            )
        ]
        assignments = [assignment_pattern] if current is block else []
        if not allowed_action_block(current, assignments, increments):
            raise ValueError("unsupported consumer side effect")
    return {
        "role": "consumer",
        "worker": loop["worker"],
        "queue": queue,
        "front": front,
        "back": back,
        "progress": progress,
        "accumulator": accumulator,
    }


def parse_role(loop):
    errors = []
    for parser in (parse_producer, parse_consumer):
        try:
            return parser(loop)
        except ValueError as exception:
            errors.append(str(exception))
    raise ValueError(" / ".join(errors))


def stream_pointer_types(text):
    result = {}
    for match in re.finditer(
        r"(?m)^\s*(unsigned\s+int|int)\s+([^;()]+)\s*;", text
    ):
        type_name = BASE.compact(match.group(1))
        for pointer in re.finditer(
            r"\*\s*([A-Za-z_]\w*)", match.group(2)
        ):
            result[pointer.group(1)] = type_name
    return result


def pointer_allocations(text, main_prefix, pointers):
    types = stream_pointer_types(text)
    if any(pointer not in types for pointer in pointers):
        raise ValueError("unresolved queue type")
    if len({types[pointer] for pointer in pointers}) != 1:
        raise ValueError("queue types differ")
    allocators = {}
    for pointer in pointers:
        matches = re.findall(
            rf"\b{re.escape(pointer)}\s*=\s*"
            r"([A-Za-z_]\w*)\s*\(\s*"
            r"([A-Za-z_]\w*)\s*\)\s*;",
            main_prefix,
        )
        if len(matches) != 1:
            raise ValueError("queue is not freshly allocated")
        allocators[pointer] = matches[0]
        assignments = re.findall(
            rf"\b{re.escape(pointer)}\s*=\s*([^;]+);", main_prefix
        )
        if len(assignments) != 1:
            raise ValueError("queue pointer is reassigned")
    allocator_names = {value[0] for value in allocators.values()}
    if len(allocator_names) != 1:
        raise ValueError("queues use different allocators")
    allocator = next(iter(allocator_names))
    body = COMPOSITE.pointer_allocator_body(text, allocator)
    if body is None or "malloc" not in body:
        raise ValueError("queue allocator is not fresh storage")
    return {
        pointer: allocators[pointer][1] for pointer in pointers
    }


def inverse_elements(first, second):
    a = re.sub(
        rf"\b{re.escape(first['progress'])}\b", "$i", first["element"]
    )
    b = re.sub(
        rf"\b{re.escape(second['progress'])}\b", "$i", second["element"]
    )
    candidates = [(a, b), (b, a)]
    for positive, negative in candidates:
        if negative in {"-" + positive, "-(" + positive + ")"}:
            return positive, negative
    raise ValueError("producer elements are not pointwise inverses")


def check_stream(text):
    cleaned = BASE.strip_comments(text)
    functions = BASE.function_bodies(cleaned)
    scope = four_worker_scope(cleaned, functions)
    loops = [
        worker_loop(worker, functions[worker]["body"])
        for worker in scope["workers"]
    ]
    roles = [parse_role(loop) for loop in loops]
    producers = [role for role in roles if role["role"] == "producer"]
    consumers = [role for role in roles if role["role"] == "consumer"]
    if len(producers) != 2 or len(consumers) != 2:
        raise ValueError("requires two producers and two consumers")
    queues = {producer["queue"] for producer in producers}
    if len(queues) != 2:
        raise ValueError("producer queues are not independent")
    by_queue = {}
    for producer in producers:
        matches = [
            consumer for consumer in consumers
            if consumer["queue"] == producer["queue"]
            and consumer["back"] == producer["back"]
            and consumer["progress"] == producer["progress"]
        ]
        if len(matches) != 1:
            raise ValueError("producer-consumer channel mismatch")
        by_queue[producer["queue"]] = matches[0]
    accumulators = {consumer["accumulator"] for consumer in consumers}
    if len(accumulators) != 1:
        raise ValueError("consumers do not share one fold")
    accumulator = next(iter(accumulators))
    types = BASE.scalar_types(cleaned)
    scalar_names = (
        {accumulator}
        | {producer["progress"] for producer in producers}
        | {producer["back"] for producer in producers}
        | {consumer["front"] for consumer in consumers}
    )
    if any(types.get(name) != "int" for name in scalar_names):
        raise ValueError("stream state is not signed int")
    if not BASE.helper_is_guarded_plus(functions):
        raise ValueError("stream fold is not guarded addition")
    main_prefix = scope["main"][:scope["first_create"]]
    if not re.search(r"\bN\s*>=\s*0\b", main_prefix):
        raise ValueError("missing nonnegative common stream bound")
    for producer in producers:
        consumer = by_queue[producer["queue"]]
        assignments = re.findall(
            rf"\b{re.escape(producer['back'])}\s*=\s*([^;]+);",
            main_prefix,
        )
        if (
            len(assignments) != 1
            or BASE.compact(assignments[0]) != consumer["front"]
        ):
            raise ValueError("queue is not initially empty")
    for variable in (
        {accumulator} | {producer["progress"] for producer in producers}
    ):
        if re.search(
            rf"\b{re.escape(variable)}\s*(?:[+\-*/]?=(?!=)|\+\+|--)",
            main_prefix,
        ):
            raise ValueError("progress or accumulator is initialized in main")
    pointer_allocations(cleaned, main_prefix, queues)
    positive, negative = inverse_elements(producers[0], producers[1])
    negative_producer = next(
        producer for producer in producers
        if re.sub(
            rf"\b{re.escape(producer['progress'])}\b",
            "$i",
            producer["element"],
        ) == negative
    )
    base_expression = negative[1:]
    int_min_guard = re.escape(base_expression.replace("$i", ""))
    normalized_body = re.sub(
        rf"\b{re.escape(negative_producer['progress'])}\b",
        "$i",
        BASE.compact(negative_producer["body"]),
    )
    guard_in_worker = (
        base_expression + ">-2147483648" in normalized_body
    )
    guard_in_main = (
        re.search(
            rf"\b{int_min_guard}\s*>\s*-2147483648\b",
            main_prefix,
        )
        is not None
        if "$i" not in base_expression
        else False
    )
    if not (guard_in_worker or guard_in_main):
        raise ValueError("inverse may negate INT_MIN")
    expression = BASE.property_expression(scope["suffix"])
    if expression != f"{accumulator}!=0":
        raise ValueError("postcondition is not cancellation identity")
    return {
        "result": "SAFE",
        "certificate": {
            "template": "phase_ordered_stream_cancellation",
            "operator": "guarded_signed_addition",
            "identity": "0",
            "positive_element": positive,
            "negative_element": negative,
            "queues": sorted(queues),
            "accumulator": accumulator,
            "channels": [
                {
                    "producer": producer["worker"],
                    "consumer": by_queue[producer["queue"]]["worker"],
                    "queue": producer["queue"],
                    "progress": producer["progress"],
                    "front": by_queue[producer["queue"]]["front"],
                    "back": producer["back"],
                    "element": producer["element"],
                }
                for producer in producers
            ],
            "obligations": {
                "all_four_workers_joined": True,
                "fresh_independent_queues": True,
                "queues_initially_empty": True,
                "common_nonnegative_bound": True,
                "commit_before_progress": True,
                "publish_and_drain_guards": True,
                "atomic_consume_and_fold": True,
                "pointwise_inverse_streams": True,
                "defined_negation": True,
                "guarded_fold_arithmetic": True,
                "zero_initial_accumulator": True,
                "exact_exit_formula": True,
            },
        },
    }


def check(text):
    composite = COMPOSITE.check(text)
    if composite["result"] == "SAFE":
        return composite
    try:
        return check_stream(text)
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
        f"STREAM_SUMMARY result={result['result']} template={template}"
    )


if __name__ == "__main__":
    main()
