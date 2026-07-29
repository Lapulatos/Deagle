# Notes: V289 Shortened-Trace Projection Attempt

## Source Finding

- The source initializes a slot-1 node with nonzero data.
- A worker can select that slot and reach the zero assertion before changing
  the stored value.
- Thus task93 has a real violation opportunity despite its expected-true
  label.

## Candidate and Semantic Failure

- V288 rejected a direct call between initialization and the first
  `pthread_create`.
- V289 relaxed only this structural admission check.
- Task91 and task93 then both produced native violation results.
- The task93 GraphML has 4,768 lines, 213,171 bytes, and SHA-256
  `993054962045ed352dc299e8e487ac215e3f641e02459daf3dd46d3e0e9cab39`.
- The trace still uses V288's shortened initialization projection: after the
  outer induction reaches two, it proceeds to worker creation, while the
  original loop must continue through nine.
- Therefore the concrete GraphML is not an execution of the original program.
  Format validity cannot repair this semantic defect.

## Gates

- Premise-breaking mutations remain inconclusive.
- Natural siblings 90--94 preserve their existing violation results.
- Prior90:
  `/data3/sujie/experiments/v289-evilcollapse-prior90-r4`, 90/90.
- V289 Exact725:
  `/data3/sujie/experiments/v289-evilcollapse-exact725-r1`.
- Contemporaneous V288 control:
  `/data3/sujie/experiments/v289-contemporaneous-v288-exact725-control-r1`.
- Exactly one status changes: task93, `ERROR -> false(unreach-call)`.
- V289 XML totals: CPU 948.065158859 seconds, wall 984.282939417 seconds,
  summed memory 25,412,145,152 bytes.
- Control XML totals: CPU 942.189970927 seconds, wall 978.256436764 seconds,
  summed memory 25,651,023,872 bytes.
- The performance gate passes, but the original-execution witness gate fails.

## Publication Boundary

- Candidate source remains only in
  `/private/tmp/deagle-v289-evilcollapse-20260729`.
- No V289 production change was committed or pushed.
- The failed experiment is preserved because failed candidates consume a
  version number.
