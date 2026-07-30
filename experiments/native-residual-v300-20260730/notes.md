# Notes: V300 Native Residual

## Baseline

- Accepted base: V299 commit `869464b795681ff44a84d5ecfe1e9999ca64fa5b`.
- Remote `deagle-dev` resolved to the same commit before this worktree was
  created.
- The user's main worktree remains untouched and contains pre-existing changes.

## Candidate Audit

- The three remaining name-comparator tasks share a generic comparator algebra
  family: antisymmetry, equality substitution, and transitivity over the same
  deterministic array-backed comparator.
- V299 already contains a structural comparator proof, but its admission
  requires the helper's failure branch to call a function with an explicit
  sink body.
- These tasks declare the standard C `abort(void)` function without supplying
  a body. The current proof therefore rejects the helper before checking the
  comparator structure.
- V300 first tests a narrow semantic correction: recognize only an unresolved,
  zero-argument, void-returning function named `abort` as the standard
  non-returning C sink. A user-defined function body is still checked by the
  existing explicit-sink audit.

## Implemented Native Admission

- The proof remains inside `deagle_exe`; the two wrapper files are byte-identical
  to V299 (`adbec275...` and `da7af28e...`).
- The admission theorem checks the full comparator scan shape rather than a
  benchmark identity: signed static key/result/current/break/index variables,
  one immutable signed array, a guarded nondeterministic loop, unit index
  progress, exact `0/+1/-1` selectors, exact subtraction order, exact result
  write census, control-flow order, worker noninterference, and pairwise worker
  isomorphism.
- The property side normalizes equality substitution, antisymmetry, and strict
  transitivity forms, including def-use through local GOTO temporaries.
- No task name, task path, YAML label, program hash, or source-line constant is
  present in the changed production files.

## Target and Negative Evidence

- The first gate candidate SHA-256 `e00826db...` was rejected after Prior90
  exposed two false-to-true regressions; it is not a release candidate.
- Current scoped candidate SHA-256:
  `549ce2ac77fe8d726d40fc7efb3b64027d017df8b16aa673e5a18d1ecc06a03f`.
- With the unchanged V299 wrapper, the three target tasks complete in
  `0.22 s`, `0.22 s`, and `0.23 s` wall time.
- The 14-mutation suite rejects every structurally invalid variant, including
  changed bounds, steps, selector constants, subtraction order, result-write
  census, triangle inputs, CFG order, and fake/user-defined abort variants.
- Each target emits a native correctness witness. Ordinary WitnessLint accepts
  all three. Strict WitnessLint cannot parse these Weaver C inputs and returns
  1; this is recorded as a validator parser limitation, not claimed as strict
  semantic certification.

## Release Evidence

- Paired Prior90 changes only the three targets from timeout to correct true;
  it has zero old-correct losses and zero new wrong results.
- Paired Exact725 changes only the same three targets, raising accepted
  adjudicated coverage from 714 to 717. CPU, wall time, and summed task memory
  improve by 15.67%, 15.61%, and 0.20% against V299.
- Two independent object-free builds produce byte-identical `deagle_exe`
  binaries with SHA-256
  `8b96d184c37d85105ad30619b412ea21704468c96f7f40ded0c4190d236f90fe`.
- The generated dashboard contains Baseline plus V1-V300, 302 ledger rows
  including the header, 589 chart points, and zero browser console errors.
- Dashboard timing also corrects inconsistent epoch fields for V295 and V296;
  the displayed ISO intervals are unchanged and V294-V300 now sort strictly.
