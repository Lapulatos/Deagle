#!/usr/bin/env python3
"""Generate generic local-clamp acceleration acceptance and rejection cases."""

from pathlib import Path
import sys


PRELUDE = r"""
typedef unsigned long pthread_t;
typedef union { char bytes[36]; long align; } pthread_attr_t;
extern int pthread_create(
  pthread_t *, const pthread_attr_t *, void *(*)(void *), void *);
extern int pthread_join(pthread_t, void **);
extern void __assert_fail(
  const char *, const char *, unsigned, const char *)
  __attribute__((noreturn));
void reach_error(void) { __assert_fail("0", "mutation.c", 1, "main"); }
"""


def program(
    initial: int,
    bound: int,
    update: str,
    expected: int,
    extra: str = "",
) -> str:
    return (
        PRELUDE
        + f"""
_Atomic int total;
_Atomic int observed;
void *worker(void *arg) {{
  int x = {initial};
  while (x < {bound}) {{
    {extra}
    {update}
  }}
  total += x;
  return 0;
}}
int main(void) {{
  pthread_t first, second;
  pthread_create(&first, 0, worker, 0);
  pthread_create(&second, 0, worker, 0);
  pthread_join(first, 0);
  pthread_join(second, 0);
  if (total != {expected})
    reach_error();
  return 0;
}}
"""
    )


def main() -> None:
    if len(sys.argv) != 2:
        raise SystemExit("usage: generate_mutations.py OUTPUT_DIR")
    output = Path(sys.argv[1])
    output.mkdir(parents=True, exist_ok=True)
    cases = {
        "accept-below-safe.c": program(3, 10, "x++;", 20),
        "accept-above-safe.c": program(12, 10, "x++;", 24),
        "accept-property-flip.c": program(3, 10, "x++;", 19),
        "reject-step-two.c": program(3, 10, "x += 2;", 22),
        "reject-extra-local.c": program(
            3, 10, "x++;", 20, "int snapshot = x; (void)snapshot;"
        ),
        "reject-shared-read.c": program(
            3, 10, "x++;", 20, "observed = x;"
        ),
    }
    for name, source in cases.items():
        (output / name).write_text(source.lstrip(), encoding="utf-8")


if __name__ == "__main__":
    main()
