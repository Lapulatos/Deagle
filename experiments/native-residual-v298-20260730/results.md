# V298 Results

## Target

| Task | Native admission | CPU | Wall | Peak RSS | Result |
|---|---:|---:|---:|---:|---:|
| `spaghetti.wvr` | 4 workers, 2 objects | 0.03 s | 0.04 s | 17,152 KiB | true |

## Release Gates

| Gate | Result |
|---|---|
| Mutation suite | 12/12 premise breaks reject; property flip fails normally |
| Prior90 | 90/90 |
| Exact725 official | 701 correct, 3 wrong, 21 unfinished |
| Exact725 adjudicated | 713 correct |
| Old-correct losses | 0 |
| New wrong results | 0 |
| CPU vs V297 | -6.920% |
| Summed wall vs V297 | -7.248% |
| Summed memory vs V297 | -0.476% |
| Peak memory | unchanged at 3,999,997,952 bytes |
| Reproducible build | byte-identical SHA-256 |
| Wrapper | byte-identical to V297 |

The only paired status change is `spaghetti.wvr.yml`, from timeout to correct
true.

## Witness

- GraphML size: 3,448 bytes.
- GraphML SHA-256:
  `91c86417d2186ccf65aa5b346e83b6f6f58498b22635274a3129b24066af2492`.
- Source SHA-256:
  `846f3fa2b3520d0013071e1a40d4401eee84eafe31e419bacc7c09bfb8abae71`.
- WitnessLint 2.1.3-dev: exit 0 format gate; source parse false and type match
  Unknown.

## Evidence Paths

- Server build:
  `/home/lapulatos/deagle-v298-terminal-overwrite-r4-final-20260730`.
- Reproducible build:
  `/home/lapulatos/deagle-v298-terminal-overwrite-r5-repro-final-20260730`.
- Mutation suite:
  `/home/lapulatos/deagle-experiments/v298-terminal-overwrite-mutations-final-r2`.
- Prior90:
  `/home/lapulatos/deagle-experiments/v298-terminal-overwrite-prior90-final-r2`.
- Exact725:
  `/home/lapulatos/deagle-experiments/v298-terminal-overwrite-exact725-final-r2`.

## Version Timing

- candidate plan birth: 2026-07-30 06:22:41 +08:00;
- final reproducible-build gate: 2026-07-30 06:50:47 +08:00;
- duration: 28.10 minutes.

The interval starts after V297's final gate at 06:11:29 and is strictly
chronological.
