# Figure Catalog

## Interactive Figure 1: Optimization Impact Timeline

- file: `deagle-optimization-impact.html`;
- purpose: compare coverage, CPU, wall, summed-memory impact, paired-memory
  impact, and observed optimization duration across baseline and V1–V182;
- data source: `optimization-impact-data.json`;
- visual encoding:
  - blue square: pristine baseline;
  - green circle: accepted optimization;
  - red diamond: rejected optimization;
  - amber triangle: audit/target gate;
  - gray cross: missing version record;
- interaction: metric switch including optimization duration,
  absolute/baseline/previous-success comparison, status filters, version range,
  hover start/end details, and searchable method ledger;
- key observation: the promoted frontier increases coverage while aggregate
  CPU/wall fall, but several full-suite failures sit off that frontier;
- caveat: missing full-suite values are deliberately absent, not zeros.

## Verification Screenshot

- file: `dashboard-verification.png`;
- viewport: 1,440 × 1,000 with full-page capture;
- checks: 183 chart timeline points, 184 ledger rows including header, hover,
  search, metric and comparison switches, zero console errors.
