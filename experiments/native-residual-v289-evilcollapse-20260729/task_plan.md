# Task Plan: V289 Shortened-Trace Projection Attempt

## Goal

Determine whether the second single-worker initialization task can be handled
by a general native Deagle extension without wrapper verdict logic, old-correct
losses, or a material resource regression.

## Acceptance Gates

- One unified `deagle_exe`; wrapper unchanged.
- No benchmark name, path, expected label, or target-line dispatch.
- Deagle owns admission, analysis, verdict, and witness generation.
- The reported execution must be feasible in the original program.
- Premise-breaking mutations reject.
- Prior90 remains 90/90.
- Exact725 loses no V288-correct result and adds no genuine wrong result.

## Phases

- [x] Create an isolated candidate from published V288.
- [x] Establish the source-level violation opportunity.
- [x] Test the native admission relaxation.
- [x] Run mutations, Prior90, and Exact725.
- [x] Compare with a contemporaneous V288 control.
- [x] Reject the candidate because its GraphML is not an original execution.

## Status

V289 is complete and failed. It changed only task93 from `ERROR` to
`false(unreach-call)` and kept Prior90 at 90/90, but the emitted path exited an
outer initialization loop after two iterations although the original bound is
ten. The four-line source change was not committed or pushed.
