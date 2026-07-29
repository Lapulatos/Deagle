# V295 Notes

## Base

- Accepted V294:
  `dec32f7bb0deca27e6229e3084ff4200f1a7487a`.
- V294 Exact725 leaves 26 unfinished tasks: 14 fast unknowns, 11 timeouts,
  and one out-of-memory result.

## Initial Candidate Set

The current candidate set is the nine Weaver timeouts left after V294:

- `array-eq-symm`
- `parallel-misc-2`
- `parallel-misc-3-extended`
- `parallel-misc-3`
- `parallel-misc-5`
- `spaghetti`
- `test-easy11`
- `unroll-cond-3`
- `unroll-cond-5`

Classification will compare their source/GOTO structures and native transform
logs before choosing an implementation.

## Structural Classification

The nine timeouts split into four semantic families:

- `test-easy11`: two event-free local unit-increment loops start from an
  arbitrary local value copied from immutable shared state and clamp that value
  to a constant bound before a joined atomic accumulation.
- `parallel-misc-2`, `parallel-misc-3`, `parallel-misc-3-extended`, and
  `parallel-misc-5`: alternating or nondeterministic shared-state recurrences.
- `array-eq-symm`, `unroll-cond-3`, and `unroll-cond-5`: relational array
  traversals with dynamic allocation or indirect indexing.
- `spaghetti`: nondeterministic modular affine recurrences over two shared
  objects.

The V294 binary trace for `test-easy11` shows the immediate cause:

- `NATIVE_LOCAL_LOOP_ACCEL applied=0 loops=0 functions=0`;
- `NATIVE_JCES applied=0 reason=induction_initialization`;
- the backend then explicitly unwinds the first worker loop thousands of
  iterations before the run times out.

The current local-loop accelerator accepts only zero-initialized induction
variables. That restriction is stronger than the exact semantics require. For
an event-free loop whose only body operation is `x++` under `x < bound`, the
terminal value is exactly `x < bound ? bound : x`. This remains exact for
signed and unsigned bit-vectors: an increment can never overflow because it is
executed only below a representable bound.

## Selected V295 Direction

Generalize the existing native local-loop acceleration from zero-initialized
counting loops to arbitrary-initial-value clamp loops. Admission remains
fail-closed:

- the induction variable is non-volatile, local, and signed or unsigned;
- the bound is a stable local scalar expression independent of the induction;
- the loop has one natural backedge and no external entry;
- the body contains exactly one unit increment and no other semantic
  instruction.

The transform replaces the loop with the exact conditional terminal
assignment. Deagle continues with its ordinary backend and owns the verdict
and witness. No wrapper change or direct certificate is involved.
