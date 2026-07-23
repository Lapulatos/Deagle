#!/usr/bin/env python3

import argparse
import importlib.util
import json
import pathlib
import re


def load_base():
    candidates = [
        pathlib.Path(__file__).resolve().with_name(
            "algebraic_segment_checker.py"
        ),
        pathlib.Path("/v87/algebraic_segment_checker.py"),
    ]
    source = next((path for path in candidates if path.exists()), None)
    if source is None:
        raise RuntimeError("missing scalar algebraic segment checker")
    spec = importlib.util.spec_from_file_location(
        "scalar_algebraic_segment_checker", source
    )
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


BASE = load_base()


def single_loop(worker, body):
    header = re.search(
        r"\bfor\s*\(\s*(?:int|unsigned\s+int)\s+([A-Za-z_]\w*)"
        r"\s*=\s*([^;]+)\s*;\s*\1\s*<\s*([^;]+)\s*;"
        r"\s*\1\s*\+\+\s*\)\s*\{",
        body,
    )
    if not header:
        raise ValueError(f"{worker}: unsupported loop")
    opening = body.find("{", header.start())
    loop_body, closing = BASE.balanced_body(body, opening)
    remainder = body[:header.start()] + body[closing + 1:]
    remainder = re.sub(r"\breturn\s+(?:0|NULL)\s*;", " ", remainder)
    if BASE.compact(BASE.strip_comments(remainder)).strip(";"):
        raise ValueError(f"{worker}: code outside loop")
    return {
        "worker": worker,
        "index": header.group(1),
        "start": BASE.compact(header.group(2)),
        "bound": BASE.compact(header.group(3)),
        "body": loop_body,
    }


def normalized(expression, index):
    return BASE.compact(
        re.sub(rf"\b{re.escape(index)}\b", "$i", expression)
    )


def exact_partition(loops, whole_bound="N", suffix_bound="N"):
    whole = [
        loop for loop in loops
        if loop["start"] == "0" and loop["bound"] == whole_bound
    ]
    prefix = [
        loop for loop in loops
        if loop["start"] == "0" and loop["bound"] == "M"
    ]
    suffix = [
        loop for loop in loops
        if loop["start"] == "M" and loop["bound"] == suffix_bound
    ]
    if len(whole) != 1 or len(prefix) != 1 or len(suffix) != 1:
        raise ValueError("ranges are not an exact segment partition")
    return whole[0], prefix[0], suffix[0]


def no_array_writes(bodies):
    return not re.search(
        r"\b[A-Za-z_]\w*\s*\[[^\]]+\]\s*"
        r"(?:[+\-*/]?=(?!=)|\+\+|--)",
        bodies,
    )


def parse_mts_update(loop, with_sum):
    body = BASE.strip_comments(loop["body"])
    body = re.sub(
        r"\b__VERIFIER_atomic_(?:begin|end)\s*\(\s*\)\s*;", " ", body
    )
    body = BASE.compact(body).strip(";")
    if with_sum:
        pattern = re.fullmatch(
            r"([A-Za-z_]\w*)=plus\(\1,(.+)\)<0\?0:\1\+(.+);"
            r"([A-Za-z_]\w*)=plus\(\4,(.+)\)",
            body,
        )
        if not pattern:
            raise ValueError("suffix is not an MTS product update")
        element1 = normalized(pattern.group(2), loop["index"])
        element2 = normalized(pattern.group(3), loop["index"])
        element3 = normalized(pattern.group(5), loop["index"])
        if len({element1, element2, element3}) != 1:
            raise ValueError("MTS suffix uses inconsistent elements")
        return {
            "mts": pattern.group(1),
            "sum": pattern.group(4),
            "element": element1,
        }
    pattern = re.fullmatch(
        r"([A-Za-z_]\w*)=plus\(\1,(.+)\)<0\?0:\1\+(.+)",
        body,
    )
    if not pattern:
        raise ValueError("worker is not an MTS update")
    element1 = normalized(pattern.group(2), loop["index"])
    element2 = normalized(pattern.group(3), loop["index"])
    if element1 != element2:
        raise ValueError("MTS update uses inconsistent elements")
    return {"mts": pattern.group(1), "element": element1}


def check_mts(text, functions, scope):
    loops = [
        single_loop(worker, functions[worker]["body"])
        for worker in scope["workers"]
    ]
    whole, prefix, suffix = exact_partition(loops)
    whole_update = parse_mts_update(whole, False)
    prefix_update = parse_mts_update(prefix, False)
    suffix_update = parse_mts_update(suffix, True)
    if len(
        {
            whole_update["element"],
            prefix_update["element"],
            suffix_update["element"],
        }
    ) != 1:
        raise ValueError("MTS workers use different elements")
    variables = [
        whole_update["mts"],
        prefix_update["mts"],
        suffix_update["mts"],
        suffix_update["sum"],
    ]
    if len(set(variables)) != 4:
        raise ValueError("MTS summaries are not independent")
    types = BASE.scalar_types(text)
    if any(types.get(variable) != "int" for variable in variables):
        raise ValueError("MTS summary type is not signed int")
    if not BASE.helper_is_guarded_plus(functions):
        raise ValueError("MTS addition is not guarded")
    main_prefix = scope["main"][:scope["first_create"]]
    if not re.search(r"\bM\s*>=\s*0\s*&&\s*M\s*<\s*N\b", main_prefix):
        raise ValueError("missing strict MTS segment bound")
    for variable in variables:
        if re.search(
            rf"\b{re.escape(variable)}\s*(?:[+\-*/]?=(?!=)|\+\+|--)",
            main_prefix,
        ):
            raise ValueError("MTS summary is not zero-initialized")
    if not no_array_writes(
        "".join(functions[worker]["body"] for worker in scope["workers"])
    ):
        raise ValueError("MTS worker writes an input array")
    expression = BASE.property_expression(scope["suffix"])
    w = re.escape(whole_update["mts"])
    p = re.escape(prefix_update["mts"])
    s = re.escape(suffix_update["mts"])
    total = re.escape(suffix_update["sum"])
    expected = rf"{w}!=\({s}<{p}\+{total}\?{p}\+{total}:{s}\)"
    if not re.fullmatch(expected, expression):
        raise ValueError("postcondition is not ordered MTS composition")
    return {
        "result": "SAFE",
        "certificate": {
            "template": "ordered_product_monoid",
            "operator": "maximum_tail_sum",
            "element": whole_update["element"],
            "whole": whole_update["mts"],
            "prefix": prefix_update["mts"],
            "suffix": suffix_update["mts"],
            "suffix_sum": suffix_update["sum"],
            "obligations": {
                "all_joined": True,
                "exact_partition": True,
                "guarded_signed_addition": True,
                "independent_summaries": True,
                "ordered_composition": True,
                "zero_initialization": True,
                "exact_exit_formula": True,
            },
        },
    }


def bool_types(text):
    result = set()
    for match in re.finditer(r"(?m)^\s*_Bool\s+([^;()]+)\s*;", text):
        for item in match.group(1).split(","):
            ids = re.findall(r"\b[A-Za-z_]\w*\b", item)
            if ids:
                result.add(ids[-1])
    return result


def parse_bool_update(loop):
    body = BASE.compact(BASE.strip_comments(loop["body"])).strip(";")
    match = re.fullmatch(
        r"([A-Za-z_]\w*)=\1&&(.+)",
        body,
    )
    if not match:
        raise ValueError("worker is not a boolean fold")
    return {
        "accumulator": match.group(1),
        "predicate": normalized(match.group(2), loop["index"]),
    }


def check_boolean(text, functions, scope):
    loops = [
        single_loop(worker, functions[worker]["body"])
        for worker in scope["workers"]
    ]
    whole, prefix, suffix = exact_partition(
        loops, whole_bound="N-1", suffix_bound="N-1"
    )
    updates = [
        parse_bool_update(loop) for loop in (whole, prefix, suffix)
    ]
    if len({update["predicate"] for update in updates}) != 1:
        raise ValueError("boolean workers use different predicates")
    accumulators = [update["accumulator"] for update in updates]
    if len(set(accumulators)) != 3:
        raise ValueError("boolean summaries are not independent")
    declared = bool_types(text)
    if any(accumulator not in declared for accumulator in accumulators):
        raise ValueError("boolean summary type mismatch")
    main_prefix = scope["main"][:scope["first_create"]]
    if not re.search(r"\bM\s*>=\s*0\s*&&\s*M\s*<\s*N\b", main_prefix):
        raise ValueError("missing boolean segment bound")
    for accumulator in accumulators:
        assignments = re.findall(
            rf"\b{re.escape(accumulator)}\s*=\s*([^;]+);",
            main_prefix,
        )
        if len(assignments) != 1 or BASE.compact(assignments[0]) not in {
            "1",
            "true",
        }:
            raise ValueError("boolean summary is not initialized true")
    if not no_array_writes(
        "".join(functions[worker]["body"] for worker in scope["workers"])
    ):
        raise ValueError("boolean worker writes an input array")
    expression = BASE.property_expression(scope["suffix"])
    w, p, s = map(re.escape, accumulators)
    if not re.fullmatch(rf"{w}!=\({p}&&{s}\)", expression):
        raise ValueError("postcondition is not boolean composition")
    return {
        "result": "SAFE",
        "certificate": {
            "template": "boolean_segment_fold",
            "operator": "and",
            "predicate": updates[0]["predicate"],
            "whole": accumulators[0],
            "prefix": accumulators[1],
            "suffix": accumulators[2],
            "obligations": {
                "all_joined": True,
                "exact_adjacent_index_partition": True,
                "same_predicate": True,
                "input_arrays_immutable": True,
                "true_initialization": True,
                "exact_exit_formula": True,
            },
        },
    }


def parse_map_update(loop):
    body = BASE.compact(BASE.strip_comments(loop["body"])).strip(";")
    match = re.fullmatch(
        r"([A-Za-z_]\w*)\[" + re.escape(loop["index"]) + r"\]=(.+)",
        body,
    )
    if not match:
        raise ValueError("worker is not a pointwise map")
    return {
        "output": match.group(1),
        "rhs": normalized(match.group(2), loop["index"]),
    }


def pointer_types(text):
    result = {}
    for match in re.finditer(
        r"(?m)^\s*(unsigned\s+int|int)\s*\*\s*([A-Za-z_]\w*)\s*;",
        text,
    ):
        result[match.group(2)] = BASE.compact(match.group(1))
    return result


def pure_pointwise_rhs(expression):
    residual = re.sub(
        r"\b[A-Za-z_]\w*\[\$i\]", "1", expression
    )
    return bool(re.fullmatch(r"[0-9()+\-*/%<>&|^~!?:]+", residual))


def pointer_initializers(main_prefix, pointer, allocator):
    assignments = re.findall(
        rf"\b{re.escape(pointer)}\s*=\s*([^;]+);", main_prefix
    )
    expected = re.compile(
        rf"{re.escape(allocator)}\s*\(\s*N\s*\)"
    )
    return (
        len(assignments) == 1
        and expected.fullmatch(assignments[0].strip()) is not None
    )


def pointer_allocator_body(text, allocator):
    marker = re.search(
        rf"\b(?:unsigned\s+int|int)\s*\*\s*"
        rf"{re.escape(allocator)}\s*\([^;{{}}]*\)\s*\{{",
        text,
    )
    if marker is None:
        return None
    opening = text.find("{", marker.start())
    body, _ = BASE.balanced_body(text, opening)
    return body


def check_pointwise(text, functions, scope):
    loops = [
        single_loop(worker, functions[worker]["body"])
        for worker in scope["workers"]
    ]
    whole, prefix, suffix = exact_partition(loops)
    updates = [
        parse_map_update(loop) for loop in (whole, prefix, suffix)
    ]
    if len({update["rhs"] for update in updates}) != 1:
        raise ValueError("pointwise workers use different functions")
    whole_output = updates[0]["output"]
    segment_output = updates[1]["output"]
    if (
        whole_output == segment_output
        or updates[2]["output"] != segment_output
    ):
        raise ValueError("pointwise output partition mismatch")
    rhs_arrays = set(re.findall(r"\b([A-Za-z_]\w*)\[\$i", updates[0]["rhs"]))
    if {whole_output, segment_output} & rhs_arrays:
        raise ValueError("pointwise output is read by the map")
    if not rhs_arrays or not pure_pointwise_rhs(updates[0]["rhs"]):
        raise ValueError("pointwise RHS is not a pure indexed expression")
    types = pointer_types(text)
    involved = rhs_arrays | {whole_output, segment_output}
    if any(name not in types for name in involved):
        raise ValueError("unresolved pointwise array type")
    if len({types[name] for name in involved}) != 1:
        raise ValueError("pointwise array types differ")
    main_prefix = scope["main"][:scope["first_create"]]
    if not re.search(r"\bM\s*>=\s*0\s*&&\s*M\s*<=\s*N\b", main_prefix):
        raise ValueError("missing pointwise segment bound")
    allocations = {}
    for pointer in involved:
        matches = re.findall(
            rf"\b{re.escape(pointer)}\s*=\s*"
            r"([A-Za-z_]\w*)\s*\(\s*N\s*\)\s*;",
            main_prefix,
        )
        if len(matches) != 1:
            raise ValueError("pointwise array is not freshly allocated")
        allocations[pointer] = matches[0]
    if len(set(allocations.values())) != 1:
        raise ValueError("pointwise arrays use different allocators")
    allocator_name = next(iter(allocations.values()))
    if any(
        not pointer_initializers(main_prefix, pointer, allocator_name)
        for pointer in involved
    ):
        raise ValueError("pointwise array is reassigned or aliased")
    allocator_body = pointer_allocator_body(text, allocator_name)
    if allocator_body is None or "malloc" not in allocator_body:
        raise ValueError("pointwise allocator is not resolved fresh storage")
    suffix_text = scope["suffix"]
    index_match = re.search(
        r"\b(?:int|unsigned\s+int)\s+([A-Za-z_]\w*)\s*="
        r"\s*__VERIFIER_nondet_(?:int|uint)\s*\(\s*\)\s*;",
        suffix_text,
    )
    if not index_match:
        raise ValueError("missing pointwise property index")
    index = index_match.group(1)
    if not re.search(
        rf"\b0\s*<=\s*{re.escape(index)}\s*&&\s*"
        rf"{re.escape(index)}\s*<\s*N\b",
        suffix_text,
    ):
        raise ValueError("pointwise property index is unbounded")
    expression = BASE.property_expression(suffix_text)
    expected = (
        re.escape(whole_output)
        + r"\["
        + re.escape(index)
        + r"\]!="
        + re.escape(segment_output)
        + r"\["
        + re.escape(index)
        + r"\]"
    )
    if not re.fullmatch(expected, expression):
        raise ValueError("postcondition is not pointwise equality")
    return {
        "result": "SAFE",
        "certificate": {
            "template": "pointwise_segment_map",
            "operator": "map",
            "rhs": updates[0]["rhs"],
            "whole_output": whole_output,
            "segment_output": segment_output,
            "property_index": index,
            "obligations": {
                "all_joined": True,
                "exact_partition": True,
                "same_pure_rhs": True,
                "fresh_distinct_outputs": True,
                "disjoint_segment_writes": True,
                "bounded_property_index": True,
                "exact_exit_formula": True,
            },
        },
    }


def check(text):
    scalar = BASE.check(text)
    if scalar["result"] == "SAFE":
        return scalar
    try:
        cleaned = BASE.strip_comments(text)
        functions = BASE.function_bodies(cleaned)
        scope = BASE.concurrency_scope(cleaned, functions)
        errors = []
        for checker in (check_mts, check_boolean, check_pointwise):
            try:
                return checker(cleaned, functions, scope)
            except ValueError as exception:
                errors.append(str(exception))
        return {
            "result": "UNKNOWN",
            "reason": " | ".join(errors),
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
        f"COMPOSITE_SUMMARY result={result['result']} "
        f"template={template}"
    )


if __name__ == "__main__":
    main()
