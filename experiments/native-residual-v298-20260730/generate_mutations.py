#!/usr/bin/env python3

import pathlib
import sys


if len(sys.argv) != 3:
    raise SystemExit("usage: generate_mutations.py SOURCE.c OUTPUT_DIR")

source = pathlib.Path(sys.argv[1]).read_text()
output = pathlib.Path(sys.argv[2])
output.mkdir(parents=True, exist_ok=True)


def one(old, new):
    if source.count(old) < 1:
        raise ValueError(f"missing mutation anchor: {old!r}")
    return source.replace(old, new, 1)


mutations = {
    "signed-object": one(
        "_Atomic unsigned int x_0, x_1;",
        "_Atomic int x_0, x_1;",
    ),
    "nonatomic-object": one(
        "_Atomic unsigned int x_0, x_1;",
        "unsigned int x_0, x_1;",
    ),
    "volatile-object": one(
        "_Atomic unsigned int x_0, x_1;",
        "volatile _Atomic unsigned int x_0, x_1;",
    ),
    "value-mismatch": one(
        "  x_0 = 0;\n\n  return 0;",
        "  x_0 = 1;\n\n  return 0;",
    ),
    "loop-assume": one(
        "    x_0 = __VERIFIER_nondet_uint();",
        "    assume_abort_if_not(x_0 == x_0);\n"
        "    x_0 = __VERIFIER_nondet_uint();",
    ),
    "address-escape": one(
        "int main() {\n",
        "int main() {\n"
        "  void *escaped = (void *)&x_0;\n"
        "  (void)escaped;\n",
    ),
    "foreign-dependency": one(
        "    x_0 += 3;",
        "    x_0 += x_1;",
    ),
    "loop-local-effect": one(
        "    x_0 = __VERIFIER_nondet_uint();",
        "    unsigned int snapshot = x_0;\n"
        "    (void)snapshot;\n"
        "    x_0 = __VERIFIER_nondet_uint();",
    ),
    "conditional-final-store": one(
        "  x_0 = 0;\n\n  return 0;",
        "  if (__VERIFIER_nondet_bool())\n"
        "    x_0 = 0;\n\n  return 0;",
    ),
    "missing-join": one(
        "  pthread_join(t4, 0);\n",
        "",
    ),
    "foreign-writer": one(
        "int main() {\n",
        "void foreign_writer(void) { x_0 = 0; }\n\n"
        "int main() {\n",
    ),
    "deterministic-loop": one(
        "  while (__VERIFIER_nondet_bool()) {",
        "  while (1) {",
    ),
    "property-flip": one(
        "  assume_abort_if_not(x_0 != x_1);",
        "  assume_abort_if_not(x_0 == x_1);",
    ),
}

for name, content in mutations.items():
    (output / f"{name}.c").write_text(content)
