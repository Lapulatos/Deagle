# Notes: V287 Pointer-Exception Scope

## Rule and Boundary

- Baseline: accepted V285, 700 official / 701 adjudicated correct.
- Worktree:
  `/private/tmp/deagle-v287-pointer-exception-scope.20260729`.
- Server workspace:
  `/data3/sujie/workspaces/deagle-v287-pointer-exception-scope-r1-20260729`.
- Candidate binary SHA-256:
  `21b2c8653c5c73733ff6e3adcb9033e5833fb6e2a797034e16fcbe083523513c`.
- Only `src/analyses/pure_spin_wait_analysis.cpp` changes.
- The original V285 admission rule remains for reservation and
  stuttering-retry candidates.
- A pointer-valued read without prior reservation is admitted only when that
  exception is unique and the whole model contains exactly one marked loop.
- Wrapper `deagle` and `deagle.py` hashes are byte-identical to V285.
- Deagle performs admission, proof, verdict, and witness generation.

## Natural and Mutation Gates

Formal environment: `deagle-rvf-p1:sujie`.

- `ticketlock`: SUCCESS, preserved.
- `cnalock`: SUCCESS, new gain.
- `rec_mcslock`, `hclhlock`, `semaphore`, `ttaslock`: rejected.
- Five negative mutations reject: second marked loop, missing start, missing
  exit, second atomic read, and effectful body call.
- Local-only bookkeeping positive control is admitted and proved.

## Prior90 and Exact725

- Prior90:
  `/data3/sujie/experiments/v287-pointer-exception-scope-prior90-r1`.
- Prior90 result: 90/90 correct, 0 incorrect, 0 unknown.
- Exact725:
  `/data3/sujie/experiments/v287-pointer-exception-scope-exact725-r1`.
- Exact XML:
  `/data3/sujie/experiments/v287-pointer-exception-scope-exact725-r1/results/exact725.2026-07-29_12-55-14.results.accepted-native-integration-exact725.Concurrency.xml.bz2`.
- Official/adjudicated correct: 701/702.
- Only delta: `libvsync/cnalock.yml`, unknown -> correct true.
- Old-correct losses: 0.
- New wrong results: 0.
- CPU: 861.356850191 -> 866.534168323 s (+0.601%).
- Summed wall: 906.056512353 -> 910.874547254 s (+0.532%).
- Summed memory: 25,645,174,784 -> 25,625,346,048 B (-0.077%).
- 48-way batch wall: 81.03 -> 81.27 s.

## Witness and Build

- Witness:
  `/data3/sujie/experiments/v287-pointer-exception-scope-witness-r1/witness.graphml`.
- Witness size: 3,223 bytes.
- Witness SHA-256:
  `c5ca053bae6ba833cd298e380f91f7293a98a2f31e158f2ebb9a75831070c55d`.
- WitnessLint 2.1.3-dev commit:
  `5297b5889b936f5eff5a1f2b594230df9a28d1c5`.
- WitnessLint exit code: 0.
- The changed translation unit compiles on macOS and Linux.
- The accepted-object baseline relinks one unified `deagle_exe`, which is the
  exact candidate used for natural, mutation, Prior90, Exact725, and witness
  gates.

## Publication

- Native commit:
  `3b02c2e0ed7854ba9d91971965dd84e77f3b2dcf`.
- Remote branch: `origin/deagle-dev`.
- Remote SHA was read back and matched the local commit exactly.
- V286's rejected source is absent from the commit.
