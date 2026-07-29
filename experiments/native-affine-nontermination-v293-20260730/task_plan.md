# V293 Native Feasibility Plan

## Objective

Increase exact725 coverage beyond V291's accepted frontier without wrapper
analysis, without any old-correct loss, and without a material resource
regression.

## Candidate 1: affine nontermination

The candidate was rejected before implementation. Its apparent nonnegative
invariant is not inductive under signed bit-vector wraparound.

## Candidate 2: high-fan-in RF selector

- [completed] Replace per-pair RF Booleans by a generic bit-vector selector
  only for reads with at least 64 candidate writes.
- [completed] Build one unified native executable.
- [completed] Compare the target against accepted V291 under identical
  4 GB and 90-second limits.
- [completed] Fix an empty-expression initialization defect found by the first
  diagnostic run.
- [completed] Reject the candidate after the corrected run still exhausted
  memory with no target completion or resource improvement.
- [completed] Restore all production source exactly to the V292 base.

## Release Boundary

- One unified `deagle_exe`.
- Wrapper remains unchanged.
- Any unsupported write, call, arithmetic width, overflow condition, or loop
  exit causes rejection.

## Decision

Failed. V293 has no production source change, no wrapper change, and no
coverage gain. Release gates beyond target feasibility were not run.
