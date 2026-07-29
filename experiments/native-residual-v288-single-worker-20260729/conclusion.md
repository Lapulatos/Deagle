# Conclusion: V288 Single-Worker Initialization Prefix

## Decision

Accepted. V288 adds one semantically adjudicated Exact725 result by exposing a
real counterexample in
`28-race_reach_91-arrayloop2_racefree.yml`. It preserves every V287 result,
keeps Prior90 at 90/90, rejects all six premise-breaking mutations, and has no
material resource regression.

## Native Ownership

- One unified `deagle_exe` performs structural admission, GOTO
  under-approximation, counterexample search, verdict, and witness generation.
- `deagle` and `deagle.py` are byte-identical to V287 and remain limited to
  bounded routing and argument selection.
- The native four-file diff contains no benchmark name, task number, expected
  result, input path, or verdict/certificate dispatch.
- Task93 remains unknown; V288 makes no claim for it.

## Exact725

- Official: 701 correct / 2 wrong / 22 unknown.
- Semantically adjudicated: 703 correct.
- Only V287 delta: task91 changes from ERROR to
  `false(unreach-call)`.
- Zero V287-correct losses and no other new wrong result.
- CPU: 865.047859952 s, 0.171% lower than V287.
- Summed wall: 908.799960988 s, 0.228% lower than V287.
- Summed memory: 25,715,208,192 B, 0.351% higher than V287.

## Counterexample Evidence

The source initializes a retained slot-1 node with `datum = j*i`; at
`i = 1, j = 1`, the value is 1. The native witness selects worker domain 1,
traverses the initialized list, takes the zero-assertion branch at source line
1046, and reaches the sole violation node. The 219,691-byte GraphML witness
passes WitnessLint as a format gate.

## Publication

- Native source commit:
  `4264197e57b726050c2d363108ade0b9dec78775`.
- Pushed branch: `origin/deagle-dev`.
- Remote SHA was read back and matched the local source commit.
