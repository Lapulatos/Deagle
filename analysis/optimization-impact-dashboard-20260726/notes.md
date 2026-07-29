# Dashboard Analysis Notes

## Evidence Inventory

- Server source:
  `/data3/sujie/experiments`
- Local evidence snapshot:
  `source-records/`
- Initial inventory:
  334 conclusion files and 1,578 conclusion/note/summary files.

## Final Inventory

- 183 dashboard rows: pristine baseline plus V1–V182.
- Statuses: 50 successful, 53 failed, 77 audit/gate, two missing records, one
  baseline.
- 60 comparable exact725 points, including seven rejected full configurations:
  V29, V82, V83, V110, V148, V172, and V180.
- All 60 summed-memory values match one preserved 725-row XML by correct/CPU/
  wall tuple with less than 0.01 seconds total CPU+wall deviation; exact XML
  paths are retained in `memory-sum-provenance.json`.
- V37 and V91 have no independent experiment record in the preserved
  snapshot; they remain visible as missing rather than being silently skipped.
- V1 and V17–V20 were recovered from unversioned/shared project-state records.
- V49 and V168 were recovered from the next version's preserved design or
  residual notes.

## Metric Semantics

- `correct`: BenchExec correct verdict count; higher is better.
- `cpu_s`: aggregate CPU seconds over the comparable exact725 round; lower is
  better unless a version deliberately trades time for additional results.
- `wall_s`: aggregate wall seconds; lower is better.
- `memory_sum_b`: sum of the 725 BenchExec per-task peak-memory values in
  bytes; lower is better. This is an aggregate suite footprint, not concurrent
  physical RAM usage.
- `timing.duration_minutes`: elapsed time between the first and last retained
  artifact for a version after excluding copied source/data/control paths and
  clamping inherited timestamps. It includes research, implementation,
  experiments, analysis, and documentation.
- `status`: promoted success, rejected failure, or audit/no implementation.

## Statistical Boundary

Most full-suite versions have one development round. The dashboard is
descriptive and provenance-oriented; it must not display confidence intervals
or significance claims that the records cannot support.

## Cumulative Descriptive Result

Against pristine Deagle, the latest promoted V181 exact725 result changes:

- correct results: 444 to 631, +187;
- aggregate CPU: 12,737.303 to 2,836.669 seconds, -77.73%;
- aggregate wall: 12,762.179 to 2,868.463 seconds, -77.52%;
- summed task memory: 68.299 GB to 39.590 GB, -42.04%.

## Optimization-Time Coverage

- 175/182 optimization versions have independent artifact-backed start/end
  windows.
- V17–V20 share one recovered project-state record and V168 shares V169's
  record; they are not assigned invented per-version durations.
- V37 and V91 have no independent experiment record.
- The observed duration is not pure LLM compute time and overlapping version
  windows must not be summed as active work.
- Rebuild boundary: `build-dashboard-data.js` consumes the preserved
  `version-time-data.json`. Regenerating that evidence file itself requires
  `node build-version-time-data.js <remote-time-audit.txt>`; an unqualified
  invocation is intentionally rejected.

This cumulative comparison reuses historical runs from different dates. It
supports a progress statement, not causal attribution of the full reduction
to any single version.
