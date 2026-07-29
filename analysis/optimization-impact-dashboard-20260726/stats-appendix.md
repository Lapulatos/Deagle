# Statistical Appendix

## Unit and Protocol

- unit: one full-tool configuration over the exact725 task suite;
- resources: 48 workers, one core/task, 4 GB/task, 60 seconds/task;
- repetitions: one development round per configuration;
- primary metrics: correct count, aggregate CPU seconds, aggregate wall
  seconds, summed task memory over 725 tasks;
- secondary memory metric: paired per-task geometric-mean change when recorded.

## Descriptive Baseline Comparison

| Metric | Pristine | V181 | Change |
|---|---:|---:|---:|
| Correct | 444 | 631 | +187 |
| CPU | 12,737.303 s | 2,836.669 s | -77.73% |
| Wall | 12,762.179 s | 2,868.463 s | -77.52% |
| Summed task memory | 68,299,001,856 B | 39,589,552,128 B | -42.04% |

## Development-Time Evidence

- independently timed optimization versions: 175/182;
- unavailable: V17–V20, V37, V91, and V168;
- timestamp source: retained server artifact mtimes after excluding copied
  source/workspace/dataset/control paths;
- interpretation: observed end-to-end research interval, not pure LLM compute
  time or a non-overlapping labor total.

## Inferential Boundary

No confidence interval, p-value, or significance test is valid from one
full-suite round per configuration. Task-level rows are repeated measures
under different tool configurations and are not treated as independent
replicates. All dashboard comparisons are descriptive.
