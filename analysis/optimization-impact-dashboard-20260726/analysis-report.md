# Deagle Optimization Impact Analysis

## Question

How did the recorded V1–V182 Deagle optimization attempts affect correct
verification completions, aggregate CPU, aggregate walltime, and memory
relative to pristine Deagle?

## Main Descriptive Findings

The dashboard contains all 182 version positions plus the pristine baseline.
Fifty versions are recorded as successful, 53 as failed, 77 as audit/gate
only, and two have no independent preserved record.

Sixty points have comparable exact725 metrics. Seven are explicitly rejected
full configurations, so the plot preserves negative results instead of
drawing only the promoted frontier.

The promoted frontier reaches V181:

- 631 correct versus baseline 444, an increase of 187;
- 2,836.669 aggregate CPU seconds versus 12,737.303, a 77.73% reduction;
- 2,868.463 aggregate wall seconds versus 12,762.179, a 77.52% reduction;
- 39.590 GB summed task memory versus 68.299 GB, a 42.04% reduction.

## Interpretation

The main improvement mechanism across the accepted frontier is conversion of
timeouts/OOM/errors into fast sound results. Many common-correct tasks are
near neutral or slightly slower in individual rounds. The cumulative CPU/wall
reduction therefore must not be described as a uniform per-task speedup.

The primary memory chart now sums all 725 BenchExec task-memory measurements.
The paired-memory geometric mean remains a secondary view of the per-task
distribution.

The dashboard also exposes artifact-backed optimization start/end timestamps
and elapsed minutes for 175 versions. These intervals capture the observable
research-to-conclusion workflow, not pure LLM inference or active coding time.

## Claim Candidates

- Claim:
  - Source evidence: pristine exact725 and V181 exact725 records.
  - Allowed wording: The recorded promoted frontier increases correct results
    by 187 and reduces aggregate CPU/wall by about 77.7% relative to the
    historical pristine run.
  - Forbidden stronger wording: Every task is 4.5x faster; the reduction is
    statistically significant; all versions are directly causal.
  - Uncertainty: one round per configuration, reused controls, different
    experiment dates.
  - Decision: keep with historical/cumulative qualifier.

- Claim:
  - Source evidence: 60 exact725 points and seven rejected full configurations.
  - Allowed wording: Several apparently promising methods failed because of
    lost correct results, common-path overhead, memory growth, or instability.
  - Forbidden stronger wording: Every rejected method is theoretically
    useless.
  - Uncertainty: many rejected methods were stopped at targeted gates.
  - Decision: keep as an experimental-process observation.
