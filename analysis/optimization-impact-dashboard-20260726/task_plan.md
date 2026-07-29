# Deagle Optimization Impact Dashboard Plan

## Goal

Produce a self-contained interactive HTML that compares the pristine Deagle
baseline with every recorded V1–V219 optimization/audit by verified-program
count, aggregate CPU, aggregate walltime, summed full-suite memory, and
artifact-backed implementation duration, while visually separating successful,
failed, and audit-only versions.

## Comparison Rules

1. Primary comparable suite: exact725, 48 workers, one core/task, 4 GB,
   60 seconds/task.
2. The pristine cloned Deagle is the global baseline.
3. A version with no exact725 round has missing resource metrics, never an
   inferred zero.
4. Runs with different task counts or limits are retained as method evidence
   but excluded from connected exact725 resource lines.
5. Success/failure follows the recorded promotion decision, not whether an
   internal counter improved.
6. Each numeric field keeps a provenance path and evidence status.
7. Total memory is the sum of all 725 BenchExec `memory` values, not the
   maximum memory of one task.
8. Optimization duration is the observed experiment-artifact time window;
   missing or shared timestamps are not estimated.

## Phases

- [x] Inventory local and server experiment records.
- [x] Extract and normalize version/method/decision/resource evidence.
- [x] Resolve pristine baseline and cumulative promoted-version series.
- [x] Generate JSON/CSV plus interactive HTML.
- [x] Validate counts, missing-data handling, hover content, filters, and
  baseline comparisons.
- [x] Recompute total memory directly from all preserved exact725 XML rows.
- [x] Audit server artifact timestamps and add per-version start/end/duration.
- [x] Deliver the artifacts and limitations.

## Status

**Updated through V290.** The dashboard has 291 embedded data rows (baseline
plus V1–V290). V256–V257 are successful rows for one
consolidated native redo endpoint: both display adjudicated coverage 685 and
the shared gain is not accumulated twice. V258–V263 are successful native-redo
rows with verifier metrics and core chart points; their historical wrapper
exact725 tuples remain separately available as wrapper evidence. Native V263
records official/adjudicated 690/691 correct, 1 wrong, and 34 unknown. V203 records
the successful Property-Relevant Concurrent Event
Cone exact725 run. V204 and V205 record residual-stage audits. V206 records a
reproduction of the rejected V182 mutex method. V207 records rejected WP
predicate synthesis: two natural gains in one family, cube/SAT growth on
another family, and no exact725 run. V208 records the failed property-seed
audit: zero new predicates, so no semantic implementation was admitted.
V209 is marked failed because its post-run source audit invalidated the
declared ablation. V210 repeats the experiment with one audited binary:
GOTO-only retains both V207 proofs, but reduces predicates on only one task and
therefore does not reach natural8 or exact725.
V289 is preserved as a failed native projection attempt; its source was not
published. V290 records the accepted original-GOTO guided replay and uses
strictly increasing V288–V290 development windows.
V211 tests cyclic GOTO seeds, retains one proof with fewer predicates, but
loses the other proof because an acyclic branch is essential.
V212 tests assertion-symbol overlap and loses both proofs because the lowered
property is a symbol-free `assert(false)` controlled by reachability.
V213 recovers property-controlling branches from CFG reachability and keeps
both proofs, but only one task has fewer predicates.
V214 identifies depth two as the minimum correct WP depth; its combined
configuration is deferred to a separately preregistered natural8 successor.
V215 runs that frozen combination on natural8, cuts diagnostic resources, but
adds no correct task or second family and is rejected before exact725.
V216 is a verdict-neutral relational proof-gap audit: it preserves two SAFE
controls and three UNKNOWN candidates, identifies missing affine and
completion-conditioned relations, and intentionally records no full-suite
resource claim.
V217 implements that guarded affine transition domain. It adds three
adjudicated-correct exact725 results with no loss, reduces aggregate CPU/wall
by 4.31%/4.25%, increases summed memory by 10.03%, and exposes a 34.7%
common-correct CPU penalty from the duplicate Python prepass. It is recorded
as a capability success while the launcher architecture remains unpromoted.
V218 integrates the same native proof into V203's existing fixed-point
subprocess and dispatches only 64 reached candidates. It preserves all three
gains, reduces CPU/wall/memory by 7.00%/6.87%/0.41% versus V203, and removes
most of V217's common-task overhead. It is recorded as a successful
full-suite optimization.
V219 audits an affine-only early-return proposal and rejects it before
implementation: recurring V218 certificates require the fixed-point runner
after template closure, while true admission failures already return early.
No benchmark or resource claim is recorded.
V220 replaces location-wide replay with a sound delta-cube worklist. It
preserves all 725 statuses and the adjudicated 656/0 result, but adds no
completion, increases aggregate CPU/wall by 0.131%/0.126%, and reduces summed
memory by only 0.009%; it is rejected and not promoted.
V221 composes V218 affine certificates with bounded error-control WP. It gains
exactly two tasks with no loss, reaches adjudicated 658/0, and reduces
CPU/wall/memory by 5.01%/4.92%/0.41%. The capability is successful; its
two-executable prototype is not promoted pending single-process integration.
V222 integrates that capability into one fixed-point executable with an
explicit V218-compatible BASE mode. It matches every V221 status at
adjudicated 658/0 and slightly reduces CPU, wall, and summed memory. V222 is
the accepted server-side baseline.
Browser verification covers metric, comparison, summed-memory, duration,
hover, search, row-count, and zero-console-error checks.
Browser verification checked metric and comparison switches, summed memory,
implementation duration, hover text, method search, and zero console errors.

V255 records a failed duplicate-candidate regression audit with an observed
6.18-minute window and no exact725 metrics. V254 remains the accepted frontier.

V256 preserves two wrapper-emitted finite encoded-race counterexamples and an
observed 7.03-minute window as portfolio evidence. They are not verifier
contributions pending native redo.

V257 similarly preserves one wrapper-emitted misaligned-index result and its
4.43-minute window without counting it as a verifier contribution.

For every later completed optimization, update this dashboard before declaring
the version complete or pushing a promotable implementation.

V240 adds serialized queue sequence correspondence. The dashboard now contains
Baseline plus V1--V240, including V220--V240 start/end times, exact725 metrics,
summed memory, method descriptions, and the two queue gains. Browser
verification passed all metric, comparison, duration, tooltip, search,
row-count, and zero-console-error checks.

## Errors Encountered

- The V290 isolated worktree does not materialize the local-only
  `source-records/` archive, so the first dashboard rebuild stopped with
  `ENOENT` before changing generated output. Rebuild uses a temporary read-only
  link to the main worktree archive and removes that link after generation.

- After V255 was added without exact725 metrics, the default x-axis sampling
  no longer rendered the literal `V254` tick label even though the V254 point
  remained present. Replace the brittle sampled-label assertion with direct
  V254 point and V255 ledger/timing assertions.
- The first Playwright run exposed escaped nested JavaScript template literals
  in the generated HTML (`Invalid or unexpected token`). The generator now
  removes only its two generator-level escapes before writing the standalone
  file; Node syntax checking and browser execution pass.
- SVG does not implement Playwright's HTMLElement-only `inner_text`. The
  verifier now uses `text_content` for chart labels.
- The first summed-memory browser assertion expected the exact baseline value
  to appear as an automatically selected y-axis tick. Axis ticks are scaled
  values and need not equal a data point. Verification now checks the exact
  JSON value and its formatted ledger cell, while the chart check verifies the
  selected metric label.
- The final reproducibility check initially invoked
  `build-version-time-data.js` without its required
  `remote-time-audit.txt` argument. This was a command error, not a data
  failure. The preserved, already-audited `version-time-data.json` remains the
  input for deterministic dashboard regeneration; raw timestamp extraction
  must be rerun only with an explicit server audit file.
- The first V240 rebuild used an undefined `memoryMetricDefinition` property
  in its manual memory evidence. It was replaced with the same
  `source_xml`/`evidence_kind` schema used by V239, then data, HTML, and browser
  verification were rerun successfully.
- The V195 browser check could not open the local standalone HTML because the
  connected browser rejected `file://` navigation. Static data and generated
  HTML checks passed; visual and console verification remain pending.
- After adding V196, the browser verifier still expected the old ledger row
  count. The actual DOM contains one header, one baseline, and 196 version
  rows, for 198 `.ledger-row` elements. The assertion was corrected and the
  full interactive verification passed.
- The first V239 regeneration invoked `build-memory-sum-provenance.js` without
  its required JSONL argument. V239's preserved XML is already registered
  directly in `build-dashboard-data.js`; deterministic data/HTML regeneration
  and the full Playwright verification then passed.
- The system Python lacked Playwright. Verification used a temporary venv and
  the existing local Chromium cache; no repository dependency was added.
- V258 retains historical wrapper evidence alongside accepted native redo:
  official/adjudicated correct 685/686, wrong 1, unknown 39, with exact725
  zero losses and zero new wrong.
- V259 retains historical wrapper evidence alongside accepted native redo:
  official/adjudicated correct 686/687, wrong 1, unknown 38, with exact725
  zero losses and zero new wrong.
- V260 retains historical wrapper evidence alongside accepted native redo:
  official/adjudicated correct 687/688, wrong 1, unknown 37, with exact725
  zero losses and zero new wrong.
- V261 retains historical wrapper evidence alongside accepted native redo:
  official/adjudicated correct 688/689, wrong 1, unknown 36, with exact725
  zero losses and zero new wrong.
- V262 retains historical wrapper evidence alongside accepted native redo:
  official/adjudicated correct 689/690, wrong 1, unknown 35, with exact725
  zero losses and zero new wrong.
- V263 retains historical wrapper evidence alongside accepted native redo:
  official/adjudicated correct 690/691, wrong 1, unknown 34, with exact725
  zero losses and zero new wrong.
- V264 is rejected at design review as task specialization; it has no exact
  metrics.
- V265 is rejected at the natural performance gate; its candidate was restored
  before prior or exact execution.
- V266 is accepted native evidence: official/adjudicated correct 691/692,
  zero losses/new wrong, CPU +0.498%, wall +0.441%, and memory +0.849%.
- V267 is accepted native evidence: T28 changes from ERROR to correct true
  with zero losses/new wrong. A separate `parallel-misc-5.wvr` timeout
  completion is classified as run variance. Official/adjudicated correct are
  693/694; CPU, wall, and memory are all below V266.
- V268 is accepted native evidence: T79 changes from ERROR to correct true
  with zero losses/new wrong. Official/adjudicated correct are 694/695; CPU
  and wall are below V267 and summed memory rises 0.115%.
- V264–V268 now have artifact-backed optimization windows. V265 uses the
  first active experiment artifact rather than the previous evening's
  pre-created directory, so restart idle time is not counted as work duration.
- V286 records the failed native single-pointer-spin candidate. Exact725 gains
  `cnalock` but loses accepted-V285 `ticketlock`, so adjudicated coverage
  remains 701 and the source is not promoted. Its 16.79-minute timing window
  starts at candidate-worktree birth and ends at the Exact725 XML end time.
- V287 scopes the pointer exception without changing the V285 paths. It adds
  only `cnalock`, reaches 701 official / 702 adjudicated correct with zero
  losses or new wrong results, and passes Prior90 plus WitnessLint.
