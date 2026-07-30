# V299 Notes

## Base

- Accepted V298:
  `b90ef66cb871963fd7c52b614347b008416ca27e`.
- Final Exact725 has 701 official correct, 713 adjudicated correct, three
  unchanged raw wrong results, and 21 unfinished tasks.

## Rejected First Direction

The `unroll-cond-3/5` subtractive loop bounds wrap when the unsigned input is
smaller than the tile width minus one. The tiled worker can then execute a very
large transition word while the scalar worker executes only a few or zero
steps. A general equivalence transform would therefore be unsound.

## Selected Direction

Audit a relational bisimulation between two joined array scans whose bounds,
initial indices, immutable arrays, equality guard, and unit progress agree
modulo operand symmetry.

## Native Implementation

- The transformation is implemented only in `deagle_exe`.
- It recognizes exactly two fully joined workers with the same two signed
  bounds and two array bases, equal private signed-index initial values,
  equality-controlled unit progress, and no extra worker effects.
- It rejects index aliasing, address escape, extra writes, type mismatches,
  lifecycle mismatches, word mismatches, and any post-join suffix other than
  the checked inequality premise followed by the reachability property.
- After proving that both deterministic scans finish with equal indices, it
  inserts an unreachable assumption after the final join. The wrapper is not
  involved in admission, proof, verdict, or witness generation.

## Target And Mutation Evidence

- The byte-identical wrapper invokes the V299 binary on the target and obtains
  `true` with a native correctness witness.
- Twelve structural mutations are all rejected by the transformation:
  disequality word, duplicate array, duplicate bound, extra index write,
  index address escape, index type mismatch, initial mismatch, missing join,
  property flip, step two, worker array write, and worker atomic operation.
- Remote evidence:
  `/data3/sujie/experiments/v299-symmetric-scan-mutations-r3/results/summary.tsv`.

## Paired-Gate Environment

- The accepted V298 archived result is 701 official / 713 adjudicated, but its
  former `/home/lapulatos` benchmark tree is unavailable on the current
  server.
- The available `/data3/sujie/svcomp2026-caat` tree gives 57 correct on
  Prior90 for both a reconstructed V298 control and V299. Direct inspection of
  a timeout shows both binaries behave the same, so this is an environment or
  dataset mismatch rather than a V299-only regression.
- A paired final Prior90 comparison reports zero status changes. V298 totals
  are 477.777 s CPU and 479.983 s wall; V299 totals are 478.895 s CPU and
  481.248 s wall, changes of about +0.23% and +0.26%.
- Paired Exact725 changes exactly one status: `array-eq-symm.wvr.yml` changes
  from wrong `false(unreach-call)` to correct `true`. The other 724 statuses
  are identical.
- Exact725 CPU changes from 1397.609 s to 1404.257 s (+0.48%), wall from
  1419.671 s to 1426.350 s (+0.47%), and summed peak memory from 100.921 GB to
  101.155 GB (+0.23%).

## Witness Boundary

Deagle emits a 3,450-byte correctness witness with SHA-256
`86159de1eb18d27846a2af16eb7fb405aa71fe7c2c21b1ba11998213153a1bb6`.
WitnessLint 2.1.3-dev exits 0 as a format gate. It reports that the source was
not parsed and the type match is Unknown, so this is not claimed as an
independent semantic proof.

## Reproducibility

- Evaluated gate binary SHA-256:
  `b7d0ee363be9b9c1cecf30016ad53c09dd85b7c8c8952c9a56d34a6a73e33afd`.
- Two independent clean builds produce the same SHA-256:
  `ea2168ae9163f05b10b745a7e0c132d5e9b8a21a99fbbfed73991d01987fa139`.
- The clean-build hash differs from the evaluated incremental build because
  clean static-library construction changes link member order and function
  addresses. Both clean source trees agree byte-for-byte; the evaluated
  binary remains the artifact tied to target, Prior90, and Exact725 results.
