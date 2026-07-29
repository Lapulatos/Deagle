#!/usr/bin/env python3
"""Generate premise-breaking controls for the V294 modular loop summary."""

from pathlib import Path
import sys


def replace_once(source: str, old: str, new: str) -> str:
    if source.count(old) != 1:
        raise ValueError(f"expected one occurrence of {old!r}")
    return source.replace(old, new, 1)


def main() -> None:
    if len(sys.argv) != 3:
        raise SystemExit("usage: generate_mutations.py INPUT OUTPUT_DIR")
    source = Path(sys.argv[1]).read_text()
    output = Path(sys.argv[2])
    output.mkdir(parents=True, exist_ok=True)

    mutations = {}
    mutations["step-two.c"] = replace_once(
        source, "x_1 = x_1 + a;", "x_1 = x_1 + a;\n    i++;"
    )
    mutations["induction-delta.c"] = replace_once(
        source, "x_1 = x_1 + a;", "x_1 = x_1 + i;"
    )
    mutations["signed-accumulator.c"] = replace_once(
        source,
        "unsigned int x_1, x_2, a, b;",
        "signed int x_1;\nunsigned int x_2, a, b;",
    )
    mutations["volatile-delta.c"] = replace_once(
        source,
        "unsigned int x_1, x_2, a, b;",
        "unsigned int x_1, x_2;\nvolatile unsigned int a;\nunsigned int b;",
    )
    mutations["extra-write.c"] = replace_once(
        source, "x_1 = x_1 + a;", "x_1 = x_1 + a;\n    x_2 = x_2 + 1;"
    )
    mutations["loop-branch.c"] = replace_once(
        source, "x_1 = x_1 + a;", "if (a) x_1 = x_1 + a;"
    )
    mutations["property-flipped.c"] = replace_once(
        source,
        "assume_abort_if_not(x_1 != x_2);",
        "assume_abort_if_not(x_1 == x_2);",
    )
    mutations["interfering-workers.c"] = replace_once(
        source, "x_2 = x_2 + b;", "x_1 = x_1 + b;"
    )

    for name, text in mutations.items():
        (output / name).write_text(text)


if __name__ == "__main__":
    main()
