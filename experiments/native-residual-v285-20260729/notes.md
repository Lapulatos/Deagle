# Notes: V285 Native Residual Portfolio

## Baseline

- Accepted remote branch: `origin/deagle-dev`.
- Accepted V284 SHA: `a379e0a17138c491be9cd4e26145373fadf2f9ef`.
- V284 exact725: 699 official / 700 adjudicated correct.
- `libvsync/cnalock.yml`: unknown.
- `libvsync/rec_mcslock.yml`: unknown and mandatory negative control.

## Historical Boundary

The rejected V278 pure-spin experiment completed `arraylock` and `cnalock`
correctly but also returned an incorrect failed verdict for `rec_mcslock`.
V285 must identify a stronger native semantic invariant; re-enabling the broad
V278 collapse is forbidden.

## Initial GOTO Diagnostics

- V285 start is fixed at the local experiment-directory birth time:
  `2026-07-29 14:44:08 +0800`, after unified V284 ended at
  `14:34:39.126 +0800`.
- V284 direct diagnostics:
  - `cnalock`: one marked pure-read spin,
    `vatomicptr_await_neq`, but no same-function reservation;
  - `rec_mcslock`: two marked pure-read spins,
    `vatomicptr_await_neq` and `vatomic32_await_eq`;
  - both are inconclusive under V284.
- The pointer exchange is in the acquire caller rather than inside the await
  helper. The V285 candidate therefore requires every direct call to the
  admitted await helper to have a native-traced atomic reservation in its
  caller prefix.
- The first candidate smoke reused a stale archive and is invalid. The second
  was correctly rebuilt but still searched only the await helper prefix; it
  remained inconclusive and motivated the caller-prefix obligation.

## First Valid Candidate

- All accepted checks run inside `deagle-rvf-p1:sujie`; host runs are invalid
  because missing multiarch headers remove the pthread bodies.
- Native admission follows every direct caller path from the pure-read await
  helper and requires an atomic fetch-add, add-fetch, or exchange reservation
  before the call on every path.
- `cnalock`:
  - one marked spin;
  - caller-path reservation proven;
  - 828 model instructions within the 850-instruction proof-cost budget;
  - `VERIFICATION SUCCESSFUL`, exit 0;
  - native witness size 3,263 bytes.
- `rec_mcslock`:
  - two marked spins;
  - both have caller-path reservations;
  - rejected by the global exactly-one-spin obligation;
  - `VERIFICATION INCONCLUSIVE`, exit 5.
- Evidence:
  `/data3/sujie/experiments/v285-cnalock-candidate-container-r2`.
- This is target-only evidence and does not authorize commit or publication.

## Rejected Candidate Boundaries

- A host-side `cnalock` run returned a 5,705-byte violation witness only
  because preprocessing failed on `bits/wordsize.h`, leaving
  `pthread_create` and `pthread_join` without bodies. The workers never ran,
  so this is an invalid pseudo-counterexample and is excluded.
- CFG dominance repair showed that a syntactically earlier exchange does not
  necessarily dominate every await call. With the repaired all-path check,
  `cnalock` is correctly restored to inconclusive.
- Residual libvsync census covered 11 V284 unknown tasks. Every task remained
  inconclusive under the sound reservation boundary.
- A diagnostic removal of the reservation requirement admitted the
  626-instruction `ttaslock` model, but it still timed out at 90 seconds and
  added no coverage. `arraylock` stayed successful and the two-spin
  `rec_mcslock` stayed inconclusive.
- The no-reservation diagnostic is rejected. It is not eligible for mutation,
  prior90, exact725, commit, or publication.
- Evidence:
  - `/data3/sujie/experiments/v285-cnalock-cfg-dominance-r1`;
  - `/data3/sujie/experiments/v285-libvsync-residual-census-r2`;
  - `/data3/sujie/experiments/v285-single-spin-small-smoke-r1`.

## Non-Spin Residual Selection

- Six LDV unknown tasks fail before verification because they contain real
  inline assembly. V280 already established that treating those instructions
  as empty compiler barriers is invalid.
- `unroll-cond-3` and `unroll-cond-5` use unsigned subtractive guards that
  wrap for small `n`; V255 already rejected a simple chunk-equivalence proof.
- `elimination_backoff_stack` reaches residual BMC but exhausts resources
  during SC constraint construction:
  - symbolic execution: 1.489 seconds;
  - SSA steps: 18,289;
  - property event cone: 9,380 events, only 72 removable;
  - dominant event families are indexed thread records, elimination
    locations, allocation slots, and stack-head accesses.
- Evidence:
  `/data3/sujie/experiments/v285-elimination-backoff-profile-r1`.

## Elimination-Stack SC Profiling

- The property-event cone retains 9,308 of 9,380 events; only 72 events are
  removable.
- SC phase timing attributes the cliff primarily to read-from construction:
  19.56 seconds of 22.96 seconds before propositional conversion.
- A selector-based RF encoding for reads with at least 64 candidate writes
  reduces expression steps from 851,175 to 167,895, but the task still
  exhausts 4 GB during propositional reduction.
- This diagnostic is not an accepted V285 implementation.
- Evidence:
  - `/data3/sujie/experiments/v285-elimination-sc-phase-profile-r1`;
  - `/data3/sujie/experiments/v285-elimination-selector-rf-r2`.

## Ticket Retry-Stuttering Proof

- `ticketlock` has two marked loops:
  - the inner owner wait is a read-only wait whose reservation is established
    by a caller-path fetch-add;
  - the outer try-acquire loop retries after a failed strong compare-exchange.
- A task-name-forced diagnostic showed that collapsing both loops makes the
  target complete, but that diagnostic was explicitly unsound and was not
  used in production.
- The production analysis instead:
  - copies the GOTO model and transitively inlines the candidate loop;
  - preserves local address identity across symbolic evaluation;
  - explores all inlined paths with conservative state and path budgets;
  - rejects any retrying path with a shared write;
  - rejects a loop-carried local read before overwrite;
  - invalidates stale path facts and dependent symbolic values on assignment;
  - requires at least one retry path and one exit path;
  - rejects weak compare-exchange;
  - requires every marked loop in the model to pass one of the native proof
    routes.

## Admission Regression and Repair

- A logging cleanup temporarily omitted the original pure-read route's
  reservation/read/exit conjunction.
- The final clean-build natural-control run caught this because
  `rec_mcslock` changed to an incorrect failure.
- The conjunction was restored before release. Direct replay then reports
  both `rec_mcslock` waits as `accepted=0`, and the global gate returns
  `VERIFICATION INCONCLUSIVE`.
- No artifact from the faulty admission is accepted.

## Final Gates

- Final clean binary:
  `a01ca0735912b4a4223455af7c7c9a30c7ec2f1c54d81a9232d86c8cdb75b5da`.
- Mutation and natural-control evidence:
  `/data3/sujie/experiments/v285-ticket-native-controls-after-admission-repair-r1`.
- Final witness evidence:
  `/data3/sujie/experiments/v285-ticket-native-final-witness-r1`.
  Ticketlock and arraylock witnesses are 3,269 and 3,267 bytes; both pass
  WitnessLint.
- Final prior90:
  `/data3/sujie/experiments/v285-ticket-native-final-prior90-r1`,
  90/90 correct.
- Final exact725:
  `/data3/sujie/experiments/v285-ticket-native-final-exact725-r1`,
  700 official / 701 adjudicated correct.
- Exact status difference from contemporaneous V284 is exactly one:
  `libvsync/ticketlock.yml`, unknown to true.
- Resource comparison against
  `/data3/sujie/experiments/v285-ticket-native-v284-control-r2`:
  CPU -0.400%, summed wall -0.907%, summed memory +0.947%, and 48-way batch
  wall +1.180%.
