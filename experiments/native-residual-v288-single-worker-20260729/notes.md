# Notes: V288 Single-Worker Initialization Prefix

## Semantic Finding

Task91 initializes list elements with `datum = j*i`. For any slot `i > 0` and
element index `j > 0`, the datum is nonzero. A worker branch asserts
`datum == 0` under the global datum lock. The lock serializes access but does
not change the nonzero initial value, so a real counterexample exists despite
the benchmark's expected-true label.

## Corrected Environment Evidence

- Invalid prior host-direct run emitted a missing `bits/wordsize.h` error,
  lacked bodies for `pthread_mutex_init` and `malloc`, generated zero VCCs, and
  cannot support an inconclusive verdict.
- Correct container rerun:
  `/data3/sujie/experiments/v288-task91-container-recheck-r1`.
- Container: `deagle-rvf-p1:sujie`.
- Result: `Property: FAILURE`.
- Witness:
  `/data3/sujie/experiments/v288-task91-container-recheck-r1/error-witness.graphml`.
- Witness size: 219,695 bytes.
- Wrapper `deagle` and `deagle.py` hashes are identical to V287.

## Migration

- Worktree:
  `/private/tmp/deagle-v288-native-single-worker.20260729`.
- Base:
  `40d6d5694b496cf631d2fbb74af99cf0327f7663`.
- Migrated native files:
  - `src/analyses/jces_analysis.cpp`
  - `src/analyses/jces_analysis.h`
  - `src/cbmc/cbmc_parse_options.cpp`
  - `src/cbmc/cbmc_parse_options.h`
- The implementation was previously repaired so no GOTO mutation occurs until
  all structural admission checks succeed.

## Target and Regression Gates

- Unified V288 binary SHA-256:
  `2cebaa2315c1ebab3a83dbccf58978dfb9eef3b6d49818f7e386037294226000`.
- Target run:
  `/data3/sujie/experiments/v288-native-single-worker-target-r1`.
- Task91: native property violation with a 219,691-byte witness.
- Task93: unknown; no unsupported verdict is claimed.
- Historical old-correct loss subset:
  `/data3/sujie/experiments/v288-native-single-worker-losses-r1`.
- Loss subset result: 9/9 correct.
- Mutation run:
  `/data3/sujie/experiments/v288-native-single-worker-mutations-r1`.
- All six premise-breaking mutations return unknown and produce no violation:
  outer bound two, inner bound two, nonzero outer initialization, extra outer
  induction write, induction address escape, and fixed worker selector.

## Prior90 and Exact725

- Prior90:
  `/data3/sujie/experiments/v288-native-single-worker-prior90-r1`.
- Prior90 result: 90/90 correct, 0 incorrect, 0 unknown.
- Exact725:
  `/data3/sujie/experiments/v288-native-single-worker-exact725-r1`.
- Only status delta against V287:
  `28-race_reach_91-arrayloop2_racefree.yml`, ERROR ->
  `false(unreach-call)`.
- Every other task is unchanged.
- Official result: 701 correct / 2 wrong / 22 unknown.
- Semantic adjudication: 703 correct after the task82 and task91 label
  disputes.
- CPU: 866.534168323 -> 865.047859952 s (-0.171%).
- Summed wall: 910.874547254 -> 908.799960988 s (-0.228%).
- Summed memory: 25,625,346,048 -> 25,715,208,192 B (+0.351%).
- 48-way batch wall: 81.27 -> 81.68 s.

## Witness Audit

- Native target witness:
  `/data3/sujie/experiments/v288-native-single-worker-target-r1/91-arrayloop2_racefree/witness.graphml`.
- Witness size: 219,691 bytes.
- SHA-256:
  `3213761caf9efabca557f42a78d66ccd15c923fb3f1ff7dc82611e07de6aa8f1`.
- WitnessLint checkout:
  `5297b5889b936f5eff5a1f2b594230df9a28d1c5`.
- WitnessLint 2.1.3-dev exits 0. It confirms a GraphML violation witness,
  matching program hash, 755 nodes, 753 edges, and one violation node.
- WitnessLint reports its known parser/type-match limitation
  (`sucessfully_parsed: False`, Type-Match Unknown), so its exit code is used
  as a format gate rather than as the semantic adjudication.
- Ordered GraphML path evidence:
  - edge 367 enters outer initialization with `i = 1`;
  - edges 384 and 396 retain inner initializations with `j = 1` and `j = 2`;
  - edge 736 gives thread 1 the worker selector value 1;
  - edges 739--751 traverse source lines 1042--1048, including the assertion
    at line 1046;
  - edge 752 reaches source line 999 and the sole violation node.
- Source semantics complete the value argument: line 1059 calls
  `new(j*i)`, line 1024 assigns that value to `datum`, and `list_add` inserts
  it into slot `i`. At `i = 1, j = 1`, the retained datum is 1. The assertion
  branch at line 1046 requires that datum to be 0, so the witnessed failure is
  a real counterexample and not merely a format-valid path.

## Native Boundary and Diff Review

- The wrapper files have no V288 diff; the verified hashes remain:
  - `deagle`:
    `f0c7db51a8760794ce03af00e6dbf02159642388fea934e736e63dc4dba7f6d9`;
  - `deagle.py`:
    `da7af28e973215a744437038633e23161047ba8ccfa66830fa28e3f759daa609`.
- The unified native binary SHA-256 was re-read from the server as
  `2cebaa2315c1ebab3a83dbccf58978dfb9eef3b6d49818f7e386037294226000`.
- The four-file native diff contains no benchmark name, task number, input
  path, expected verdict, certificate, or correctness-label dispatch.
- All structural admission checks finish before mutation. The transform then
  keeps one admitted worker, restricts the initialization outer domain to two,
  fixes the representative worker to retained domain 1, and fully unwinds the
  structurally discovered inner loop in the native rescue child.
- `git diff --check` passes.

## Dashboard Verification

- Published range: Baseline plus V1--V288.
- Embedded data rows: 289.
- Ledger rows including header: 290.
- Chart points: 565.
- Browser console errors: 0.
- Checked interactions: metric switch, comparison mode, summed memory,
  optimization duration, hover tooltip, and method search.
- The isolated worktree's default `/usr/bin/python3` lacks Playwright. This is
  an environment-only failure; rerunning the same verifier against the
  isolated files with `/opt/anaconda3/bin/python3` passes all checks.
