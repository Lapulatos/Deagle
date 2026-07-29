# V298 Notes

## Base

- Accepted V297:
  `b8e8acccb8bbd2032ab5bbbf313cfd1c926c6232`.
- Final Exact725 has 700 official correct, 712 adjudicated correct, three
  unchanged raw wrong results, and 22 unfinished tasks.

## Residual Inventory

The 22 unfinished tasks split into:

- six Linux-driver front-end unknowns;
- eight libvsync fast unknowns;
- seven 60-second timeouts and one 4 GB out-of-memory task.

V292 already rejected front-end lowering and SafeStack bounded progress. V293
already rejected the elimination-backoff selector because it retained the 4 GB
cliff. The remaining Weaver timeouts divide into relational array traversals,
one nontermination invariant, and one terminal-overwrite family.

## Selected Direction

V298 implements joined terminal overwrite from GOTO structure. Every admitted
worker has:

- one local nondeterministic Boolean loop guard with a feasible zero-iteration
  exit;
- only direct operations on one non-volatile atomic unsigned scalar in the
  loop;
- no call, assumption, assertion, pointer dereference, address escape, or
  second shared dependency;
- one unconditional constant store after the loop;
- a complete create/join lifecycle, with equal terminal values for all workers
  that own the same object.

For terminating workers, the post-join state is exactly the terminal constants.
Nonterminating workers cannot pass their joins. Deagle replaces the lifecycle
with those exact stores and sends the result through its ordinary backend for
the final verdict and witness.

## Target and Negative Controls

- Evaluated binary:
  `008f6771c998e967dd3908a4d420c5fc84950db0b44d979a992909e233dffe61`.
- The target applies with four workers and two objects and completes in
  0.03 seconds CPU, 0.04 seconds wall, and 17,152 KiB peak RSS.
- Twelve premise-breaking mutations reject: address escape, conditional final
  store, deterministic guard, cross-object dependency, foreign writer,
  in-loop assumption, in-loop local effect, missing join, non-atomic object,
  signed object, unequal terminal values, and volatile object.
- A property flip remains admitted and the ordinary backend reports
  `VERIFICATION FAILED`.
- `svcomp_stuff/deagle` and `svcomp_stuff/deagle.py` remain byte-identical to
  V297.

## Formal Gates

- Prior90: 90/90, with 80 correct true, 10 correct false, and no incorrect or
  unknown result.
- Exact725: 701 official correct, 713 adjudicated correct, three unchanged raw
  wrong results, and 21 unfinished.
- Only `spaghetti.wvr.yml` changes, from timeout to correct true.
- There are zero old-correct losses and zero new wrong results.
- Against V297, CPU changes -6.920%, summed wall -7.248%, summed memory
  -0.476%, and peak memory remains 3,999,997,952 bytes.
- Two independent builds produce the same evaluated binary hash.

## Witness Boundary

Deagle emits a 3,448-byte correctness witness with SHA-256
`91c86417d2186ccf65aa5b346e83b6f6f58498b22635274a3129b24066af2492`.
WitnessLint 2.1.3-dev exits 0 as a format gate. It reports that the source was
not parsed and the type match is Unknown, so this is not claimed as independent
semantic witness validation.
