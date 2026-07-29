#!/usr/bin/env python3
"""Generate premise-breaking variants for bounded alternating cancellation."""

from pathlib import Path
import re
import sys


def replace_once(source: str, old: str, new: str) -> str:
    if source.count(old) != 1:
        raise ValueError(f"expected one occurrence of {old!r}")
    return source.replace(old, new)


def main() -> None:
    if len(sys.argv) != 3:
        raise SystemExit(
            "usage: generate_mutations.py SOURCE OUTPUT_DIR"
        )
    source = Path(sys.argv[1]).read_text(encoding="utf-8")
    output = Path(sys.argv[2])
    output.mkdir(parents=True, exist_ok=True)
    second_start = source.index("void* thread2")
    second_end = source.index("int main()", second_start)
    shared_phase = (
        source[:second_start]
        + re.sub(
            r"\bd2\b", "d1", source[second_start:second_end]
        )
        + source[second_end:]
    )

    cases = {
        "reject-odd-factor.c": source.replace(
            "2 * N", "3 * N"
        ),
        "reject-asymmetric-weight.c": replace_once(
            source, "pos -= 2;", "pos -= 3;"
        ),
        "reject-nonzero-induction.c": replace_once(
            source,
            "pos == i1 && pos == i2 && pos == 0",
            "pos == 0 && i1 == 1 && i2 == 0",
        ),
        "reject-shared-phase.c": shared_phase,
        "reject-nonatomic-object.c": replace_once(
            source, "_Atomic unsigned int pos;", "unsigned int pos;"
        ),
        "reject-extra-shared-step.c": replace_once(
            source, "d1 = !d1;", "pos += 4; d1 = !d1;"
        ),
        "reject-conditional-initialization.c": replace_once(
            source,
            "assume_abort_if_not( pos == i1 && pos == i2 && pos == 0 );",
            "if (__VERIFIER_nondet_bool()) "
            "assume_abort_if_not( pos == i1 && pos == i2 && pos == 0 );",
        ),
        "reject-self-dependent-bound.c": replace_once(
            source, "i1 < ( 2 * N )", "i1 < ( 2 * i1 )"
        ),
        "reject-late-bound-write.c": replace_once(
            source,
            "pthread_join(t1, 0);",
            "N = 0; pthread_join(t1, 0);",
        ),
        "accept-property-flip.c": replace_once(
            source,
            "assume_abort_if_not( pos != 0 );",
            "assume_abort_if_not( pos == 0 );",
        ),
    }
    for name, mutated in cases.items():
        if mutated == source:
            raise ValueError(f"mutation {name} made no change")
        (output / name).write_text(mutated, encoding="utf-8")


if __name__ == "__main__":
    main()
