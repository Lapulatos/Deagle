# V292 Native Residual Coverage Plan

## Objective

Increase exact725 coverage beyond accepted V291 without changing wrapper
analysis or verdict behavior, without losing any previously correct task, and
without a material resource regression.

## Constraints

- Use one unified `deagle_exe`.
- Keep the Python wrapper limited to bounded routing and argument selection.
- Deagle native code owns admission, proof, verdict, and witness generation.
- Add no benchmark names, paths, expected labels, or source-line constants.
- Reject the candidate on any old-correct loss or new genuine wrong result.
- Publish only after target, negative-control, Prior90, exact725, witness, and
  paired-resource gates pass.

## Work

- [completed] Diagnose the remaining short-running libvsync UNKNOWN tasks
  against accepted V291.
- [completed] Test a type-general single pure-read admission boundary.
- [completed] Test bounded-progress feasibility on residual timeout tasks.
- [completed] Reject both candidates before production implementation because
  neither can complete a new target inside the release limit.
- [completed] Preserve V292 as a failed, unpublished-code experiment.

## Priority

- P0: zero old-correct losses and no wrapper verdict logic.
- P1: one or more genuine coverage gains with bounded resource change.
- P2: preserve diagnostics for rejected candidate attempts.

## Decision

Failed. V292 adds no production source change and therefore does not run
Prior90 or exact725 release gates. Its diagnostics remain immutable evidence.
