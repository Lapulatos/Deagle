#!/usr/bin/env node

const fs = require("fs");
const path = require("path");
const { execFileSync } = require("child_process");

const here = __dirname;
const recordsRoot = path.join(here, "source-records");
const repoRoot = path.resolve(here, "../..");
const versionTimeArtifact = JSON.parse(
  fs.readFileSync(path.join(here, "version-time-data.json"), "utf8")
);
const versionTimes = new Map(
  versionTimeArtifact.rows.map((row) => [row.version, row])
);
const memorySumArtifact = JSON.parse(
  fs.readFileSync(path.join(here, "memory-sum-provenance.json"), "utf8")
);
const memorySumEvidence = new Map(
  memorySumArtifact.rows.map((row) => [row.version, row])
);
memorySumEvidence.set(196, {
  version: 196,
  memory_sum_b: 33788190720,
  source_xml:
    "../../experiments/dynamic-initialization-rf-v196-20260727/full-v196-results/results/full-v196.2026-07-26_18-50-27.results.v196-method.Concurrency.xml.bz2",
  evidence_kind: "local_preserved_exact725_xml",
});
memorySumEvidence.set(197, {
  version: 197,
  memory_sum_b: 33622917120,
  source_xml:
    "../../experiments/dynamic-object-candidate-guards-v197-20260727/full-v197-results/results/full-v197.2026-07-26_19-09-05.results.v197-method.Concurrency.xml.bz2",
  evidence_kind: "local_preserved_exact725_xml",
});
memorySumEvidence.set(199, {
  version: 199,
  memory_sum_b: 33674092544,
  source_xml:
    "../../experiments/conditional-event-generation-v199-20260727/full-v199-results/results/full-v199.2026-07-26_19-32-22.results.v199-method.Concurrency.xml.bz2",
  evidence_kind: "local_preserved_exact725_xml",
});
memorySumEvidence.set(200, {
  version: 200,
  memory_sum_b: 33739116544,
  source_xml:
    "../../experiments/dereference-local-event-guards-v200-20260727/full-v200-results/full-v200.2026-07-26_20-05-42.results.v200-method.Concurrency.xml.bz2",
  evidence_kind: "local_preserved_exact725_xml",
});
memorySumEvidence.set(203, {
  version: 203,
  memory_sum_b: 26844622848,
  source_xml:
    "../../experiments/property-relevant-event-cone-v203-20260727/full-v203-results/full-v203.2026-07-26_21-21-03.results.v203-method.Concurrency.xml.bz2",
  evidence_kind: "local_preserved_exact725_xml",
});
memorySumEvidence.set(217, {
  version: 217,
  memory_sum_b: 29535916032,
  source_xml:
    "../../experiments/guarded-affine-transition-certificate-v217-20260727/full-v217-results/full-v217-resultsfull-v217.2026-07-27_01-01-55.results.v217-guarded-affine.Concurrency.xml.bz2",
  evidence_kind: "local_preserved_exact725_xml",
});
memorySumEvidence.set(218, {
  version: 218,
  memory_sum_b: 26734747648,
  source_xml:
    "../../experiments/integrated-affine-dispatch-v218-20260727/full-v218-results/full-v218.2026-07-27_02-19-16.results.v218-integrated-affine.Concurrency.xml.bz2",
  evidence_kind: "local_preserved_exact725_xml",
});
memorySumEvidence.set(220, {
  version: 220,
  memory_sum_b: 26732269568,
  source_xml:
    "../../experiments/delta-cube-fixedpoint-worklist-v220-20260727/full-v220-results/full-v220.2026-07-27_02-53-25.results.v220-delta-cube.Concurrency.xml.bz2",
  evidence_kind: "local_preserved_exact725_xml",
});
memorySumEvidence.set(221, {
  version: 221,
  memory_sum_b: 26623918080,
  source_xml:
    "../../experiments/post-affine-residual-attribution-v221-20260727/full-v221-results/full-v221.2026-07-27_03-40-52.results.v221-combined.Concurrency.xml.bz2",
  evidence_kind: "local_preserved_exact725_xml",
});
memorySumEvidence.set(222, {
  version: 222,
  memory_sum_b: 26560638976,
  source_xml:
    "../../experiments/single-process-combined-proof-v222-20260727/full-v222-results/full-v222.2026-07-27_04-15-09.results.v222-single-process.Concurrency.xml.bz2",
  evidence_kind: "local_preserved_exact725_xml",
});
memorySumEvidence.set(225, {
  version: 225,
  memory_sum_b: 26571001856,
  source_xml:
    "../../experiments/finite-constant-protocol-product-v225-20260727/full-v225-results/full-v225.2026-07-27_05-44-34.results.v225-finite-product.Concurrency.xml.bz2",
  evidence_kind: "local_preserved_exact725_xml",
});
memorySumEvidence.set(226, {
  version: 226,
  memory_sum_b: 26072727552,
  source_xml:
    "../../experiments/preprocessed-atomic-dispatch-v226-20260727/full-v226-results/full-v226.2026-07-27_05-52-22.results.v226-preprocessed-dispatch.Concurrency.xml.bz2",
  evidence_kind: "local_preserved_exact725_xml",
});
memorySumEvidence.set(233, {
  version: 233,
  memory_sum_b: 25765847040,
  source_xml:
    "../../experiments/ticket-lock-ownership-v233-20260727/full-v233-results/full-v233.2026-07-27_07-54-26.results.v233-ticket-ownership.Concurrency.xml.bz2",
  evidence_kind: "local_preserved_exact725_xml",
});
memorySumEvidence.set(234, {
  version: 234,
  memory_sum_b: 26248269824,
  source_xml:
    "../../experiments/ticket-lock-dispatch-v234-20260727/full-v234-results/full-v234.2026-07-27_08-10-21.results.v234-ticket-dispatch.Concurrency.xml.bz2",
  evidence_kind: "local_preserved_exact725_xml",
});
memorySumEvidence.set(237, {
  version: 237,
  memory_sum_b: 26592956416,
  source_xml:
    "../../experiments/index-region-ownership-v237-20260727/full-v237-results/full-v237.2026-07-27_08-53-45.results.v237-index-region.Concurrency.xml.bz2",
  evidence_kind: "local_preserved_exact725_xml",
});
memorySumEvidence.set(238, {
  version: 238,
  memory_sum_b: 26244182016,
  source_xml:
    "../../experiments/post-store-stable-cell-v238-20260727/full-v238-results/full-v238.2026-07-27_09-34-50.results.v238-post-store-stable-cell.Concurrency.xml.bz2",
  evidence_kind: "local_preserved_exact725_xml",
});
memorySumEvidence.set(239, {
  version: 239,
  memory_sum_b: 25972404224,
  source_xml:
    "../../experiments/stack-capacity-invariant-v239-20260727/full-v239-results/full-v239.2026-07-27_10-14-52.results.v239-stack-capacity.Concurrency.xml.bz2",
  evidence_kind: "local_preserved_exact725_xml",
});
memorySumEvidence.set(240, {
  version: 240,
  memory_sum_b: 24954265600,
  source_xml:
    "../../experiments/queue-sequence-correspondence-v240-20260727/full-v240-results/full-v240.2026-07-27_10-38-12.results.v240-queue-sequence.Concurrency.xml.bz2",
  evidence_kind: "local_preserved_exact725_xml",
});
memorySumEvidence.set(241, {
  version: 241,
  memory_sum_b: 24954265600,
  source_xml:
    "../../experiments/queue-sequence-correspondence-v240-20260727/full-v240-results/full-v240.2026-07-27_10-38-12.results.v240-queue-sequence.Concurrency.xml.bz2",
  evidence_kind: "rejected_round_inherits_accepted_v240_baseline",
});
memorySumEvidence.set(242, {
  version: 242,
  memory_sum_b: 24954265600,
  source_xml:
    "../../experiments/queue-sequence-correspondence-v240-20260727/full-v240-results/full-v240.2026-07-27_10-38-12.results.v240-queue-sequence.Concurrency.xml.bz2",
  evidence_kind: "rejected_round_inherits_accepted_v240_baseline",
});
memorySumEvidence.set(243, {
  version: 243,
  memory_sum_b: 24991068160,
  source_xml:
    "../../experiments/nonnegative-oscillator-monitor-v243-20260727/full-v243-results/full-v243.2026-07-27_11-53-05.results.v243-oscillator-monitor.Concurrency.xml.bz2",
  evidence_kind: "local_preserved_exact725_xml",
});
memorySumEvidence.set(244, {
  version: 244,
  memory_sum_b: 24991068160,
  source_xml:
    "../../experiments/nonnegative-oscillator-monitor-v243-20260727/full-v243-results/full-v243.2026-07-27_11-53-05.results.v243-oscillator-monitor.Concurrency.xml.bz2",
  evidence_kind: "rejected_round_inherits_accepted_v243_baseline",
});
memorySumEvidence.set(245, {
  version: 245,
  memory_sum_b: 25394925568,
  source_xml:
    "../../experiments/dynamic-tls-calloc-zero-v245-20260727/full-v245-results/full-v245.2026-07-27_12-05-02.results.v245-dynamic-tls-calloc.Concurrency.xml.bz2",
  evidence_kind: "local_preserved_exact725_xml",
});
memorySumEvidence.set(246, {
  version: 246,
  memory_sum_b: 25456803840,
  source_xml:
    "../../experiments/tls-destructor-counterexample-v246-20260727/full-v246-results/full-v246.2026-07-27_12-14-53.results.v246-tls-destructor.Concurrency.xml.bz2",
  evidence_kind: "local_preserved_exact725_xml",
});
memorySumEvidence.set(247, {
  version: 247,
  memory_sum_b: 25774977024,
  source_xml:
    "../../experiments/partitioned-count-reduction-v247-20260727/full-v247-results/full-v247.2026-07-27_12-30-53.results.v247-partition-count.Concurrency.xml.bz2",
  evidence_kind: "local_preserved_exact725_xml",
});
memorySumEvidence.set(248, {
  version: 248,
  memory_sum_b: 25715171328,
  source_xml:
    "../../experiments/finite-two-sided-disjunction-v248-20260727/full-v248-results/full-v248.2026-07-27_12-43-10.results.v248-finite-two-sided.Concurrency.xml.bz2",
  evidence_kind: "local_preserved_exact725_xml",
});
memorySumEvidence.set(249, {
  version: 249,
  memory_sum_b: 25680318464,
  source_xml:
    "../../experiments/completion-flag-arithmetic-v249-20260727/full-v249-results/full-v249.2026-07-27_12-51-20.results.v249-completion-arithmetic.Concurrency.xml.bz2",
  evidence_kind: "local_preserved_exact725_xml",
});
memorySumEvidence.set(250, {
  version: 250,
  memory_sum_b: 25627951104,
  source_xml:
    "../../experiments/nonzero-cas-seed-v250-20260727/full-v250-results/full-v250.2026-07-27_13-02-39.results.v250-nonzero-cas.Concurrency.xml.bz2",
  evidence_kind: "local_preserved_exact725_xml",
});
memorySumEvidence.set(251, {
  version: 251,
  memory_sum_b: 25679564800,
  source_xml:
    "../../experiments/monotone-chunk-maximum-v251-20260727/full-v251-results/full-v251.2026-07-27_13-11-54.results.v251-chunk-max.Concurrency.xml.bz2",
  evidence_kind: "local_preserved_exact725_xml",
});
memorySumEvidence.set(252, {
  version: 252,
  memory_sum_b: 25302093824,
  source_xml:
    "../../experiments/linear-tiled-copy-equivalence-v252-20260727/full-v252-results/full-v252.2026-07-27_13-38-36.results.v252-tiled-copy.Concurrency.xml.bz2",
  evidence_kind: "local_preserved_exact725_xml",
});
memorySumEvidence.set(253, {
  version: 253,
  memory_sum_b: 25216737280,
  source_xml:
    "../../experiments/atomic-queue-occupancy-value-v253-20260727/full-v253-results/full-v253.2026-07-27_13-52-29.results.v253-queue-value.Concurrency.xml.bz2",
  evidence_kind: "local_preserved_exact725_xml",
});
memorySumEvidence.set(254, {
  version: 254,
  memory_sum_b: 24696680448,
  source_xml:
    "../../experiments/isomorphic-modular-fold-pair-v254-20260727/full-v254-results/full-v254.2026-07-27_14-03-38.results.v254-fold-pair.Concurrency.xml.bz2",
  evidence_kind: "local_preserved_exact725_xml",
});
memorySumEvidence.set(256, {
  version: 256,
  memory_sum_b: 24467214336,
  source_xml:
    "../../experiments/encoded-race-counterexample-v256-20260727/full-v256-results/full-v256.2026-07-27_14-36-38.results.v256-encoded-race.Concurrency.xml.bz2",
  evidence_kind: "source_xml",
});
memorySumEvidence.set(257, {
  version: 257,
  memory_sum_b: 24502198272,
  source_xml:
    "../../experiments/misaligned-index-lock-counterexample-v257-20260727/full-v257-results/full-v257.2026-07-27_14-46-42.results.v257-index-lock.Concurrency.xml.bz2",
  evidence_kind: "source_xml",
});
memorySumEvidence.set(258, {
  version: 258,
  memory_sum_b: 24514752512,
  source_xml:
    "../../experiments/same-slot-different-lock-counterexample-v258-20260727/full-v258-results/full-v258.2026-07-27_14-55-50.results.v258-slot-lock.Concurrency.xml.bz2",
  evidence_kind: "source_xml",
});
memorySumEvidence.set(259, {
  version: 259,
  memory_sum_b: 24574001152,
  source_xml:
    "../../experiments/cross-slot-list-splice-counterexample-v259-20260727/full-v259-results/full-v259.2026-07-27_15-15-23.results.v259-list-splice.Concurrency.xml.bz2",
  evidence_kind: "source_xml",
});
memorySumEvidence.set(260, {
  version: 260,
  memory_sum_b: 24667418624,
  source_xml:
    "../../experiments/independent-object-lock-index-counterexample-v260-20260727/full-v260-results/full-v260.2026-07-27_15-28-25.results.v260-object-lock-index.Concurrency.xml.bz2",
  evidence_kind: "source_xml",
});
memorySumEvidence.set(261, {
  version: 261,
  memory_sum_b: 24465362944,
  source_xml:
    "../../experiments/wrapped-mutex-zero-sum-safety-v261-20260727/full-v261-results/full-v261.2026-07-27_15-44-43.results.v261-wrapped-zero-sum.Concurrency.xml.bz2",
  evidence_kind: "source_xml",
});
memorySumEvidence.set(262, {
  version: 262,
  memory_sum_b: 24557170688,
  source_xml:
    "../../experiments/guard-dominated-common-mutex-safety-v262-20260727/full-v262-results/full-v262.2026-07-27_15-54-22.results.v262-guarded-common-mutex.Concurrency.xml.bz2",
  evidence_kind: "source_xml",
});
memorySumEvidence.set(263, {
  version: 263,
  memory_sum_b: 27473588224,
  source_xml:
    "/data3/sujie/experiments/native-redo-v256-v263-20260728/v263/full-v263-native-real-results/full-v263-native.2026-07-28_05-29-02.results.v255-conserved-sum.Concurrency.xml.bz2",
  evidence_kind: "remote_native_redo_xml",
});
memorySumEvidence.set(266, {
  version: 266,
  memory_sum_b: 27706974208,
  source_xml:
    "/data3/sujie/experiments/mutex-zero-fixedpoint-safety-v266-20260728/full-v266-results/full-v266.2026-07-28_06-25-56.results.v266-mutex-zero-fixedpoint.Concurrency.xml.bz2",
  evidence_kind: "remote_native_result_xml",
});
memorySumEvidence.set(267, {
  version: 267,
  memory_sum_b: 27560644608,
  source_xml:
    "../../experiments/singleton-function-pointer-zero-sum-v267-20260728/full-v267.xml.bz2",
  evidence_kind: "local_preserved_exact725_xml",
});
memorySumEvidence.set(268, {
  version: 268,
  memory_sum_b: 27592212480,
  source_xml:
    "../../experiments/indexed-lock-zero-sum-v268-20260728/full-v268.xml.bz2",
  evidence_kind: "local_preserved_exact725_xml",
});

function readIfExists(file) {
  return fs.existsSync(file) ? fs.readFileSync(file, "utf8") : "";
}

function lastVersion(name) {
  const versions = [...name.matchAll(/v(\d+)/gi)].map((match) =>
    Number(match[1])
  );
  return versions.length ? versions[versions.length - 1] : null;
}

function humanize(slug) {
  return slug
    .replace(/-202607\d+$/i, "")
    .replace(/-v\d+$/i, "")
    .replace(/\bvs-v\d+-full\b/gi, "")
    .replace(/\bfull\b/gi, "")
    .replace(/\baudit\b/gi, "")
    .replace(/\bintegration\b/gi, "")
    .replace(/\bgate\b/gi, "")
    .replace(/\bfeasibility\b/gi, "")
    .split("-")
    .filter(Boolean)
    .map((word) =>
      /^(jces|jpeq|rvf|goto|cas|cpu|cfg|rmw)$/i.test(word)
        ? word.toUpperCase()
        : word[0].toUpperCase() + word.slice(1)
    )
    .join(" ")
    .replace(/\s+/g, " ")
    .trim();
}

function firstEvidenceParagraph(text) {
  const paragraphs = text
    .replace(/\r/g, "")
    .split(/\n\s*\n/)
    .map((part) =>
      part
        .split("\n")
        .filter((line) => !line.trim().startsWith("#"))
        .join(" ")
        .replace(/[`*_]/g, "")
        .replace(/\s+/g, " ")
        .trim()
    )
    .filter(
      (part) =>
        part.length > 25 &&
        !part.startsWith("|") &&
        !/^Open\b|^Pending\b/i.test(part)
    );
  return (paragraphs[0] || "No narrative conclusion was recorded.").slice(
    0,
    520
  );
}

function classify(text) {
  const lower = text.toLowerCase();
  if (
    /\breject(?:ed)?\b|do not (?:merge|promote|retain)|no method or optimization claim|promoted commit:\s*none/.test(
      lower
    )
  )
    return "failed";
  if (
    /\baccept(?:ed)?(?: and promote)?\b|\bpromote\b|\bretain and push\b|\badopt\b/.test(
      lower
    ) &&
    !/authorize .{0,60}(?:full|725)|only a later .{0,60}725/.test(lower)
  )
    return "successful";
  return "audit";
}

function numbers(text) {
  return [...text.matchAll(/-?\d[\d,]*(?:\.\d+)?/g)].map((match) =>
    Number(match[0].replace(/,/g, ""))
  );
}

function pairCandidates(text, labels) {
  const lines = text.split("\n");
  const result = [];
  for (const line of lines) {
    if (!labels.some((label) => label.test(line))) continue;
    const values = numbers(line);
    if (values.length >= 2) result.push({ line: line.trim(), values });
  }
  return result;
}

function chooseCorrect(text) {
  const candidates = pairCandidates(text, [
    /\bcorrect\b/i,
    /correct results/i,
    /correct completions/i,
  ]);
  let best = null;
  for (const candidate of candidates) {
    const plausible = candidate.values.filter(
      (value) => Number.isInteger(value) && value >= 400 && value <= 725
    );
    if (plausible.length < 2) continue;
    const pair = plausible.slice(0, 2);
    if (!best || pair[1] > best.method)
      best = {
        control: pair[0],
        method: pair[1],
        evidence: candidate.line,
      };
  }
  return best;
}

function chooseSeconds(text, kind) {
  const labels =
    kind === "cpu"
      ? [/\bCPU sum\b/i, /\btotal CPU\b/i, /\baggregate CPU\b/i, /^- CPU:/i]
      : [
          /\bWall sum\b/i,
          /\btotal wall\b/i,
          /\baggregate wall\b/i,
          /^- wall:/i,
        ];
  const candidates = pairCandidates(text, labels);
  let best = null;
  for (const candidate of candidates) {
    const plausible = candidate.values.filter(
      (value) => value >= 1000 && value <= 30000
    );
    if (plausible.length < 2) continue;
    const pair = plausible.slice(0, 2);
    if (!best || pair[1] > best.method)
      best = {
        control: pair[0],
        method: pair[1],
        evidence: candidate.line,
      };
  }
  return best;
}

function choosePeakMemory(text) {
  const candidates = pairCandidates(text, [/\bpeak memory\b/i]);
  for (const candidate of candidates.reverse()) {
    let values = candidate.values.filter((value) => value > 100);
    if (!values.length) continue;
    let value = values[values.length - 1];
    if (/\bGB\b/i.test(candidate.line) && value < 100) value *= 1e9;
    else if (/\bMB\b/i.test(candidate.line) && value < 1e8) value *= 1e6;
    return { method: value, evidence: candidate.line };
  }
  return null;
}

function chooseMemoryDelta(text) {
  const patterns = [
    /paired memory(?: geometric mean| geomean)?(?: method\/control)?(?: ratio)?[^.\n]*?(-?\d+(?:\.\d+)?)%/gi,
    /paired memory[^.\n]*?(?:decrease|falls?|lower)[^.\n]*?(\d+(?:\.\d+)?)%/gi,
    /paired memory[^.\n]*?(?:increase|rises?|higher)[^.\n]*?(\d+(?:\.\d+)?)%/gi,
  ];
  for (let index = 0; index < patterns.length; ++index) {
    const matches = [...text.matchAll(patterns[index])];
    if (!matches.length) continue;
    const match = matches[matches.length - 1];
    const raw = Number(match[1]);
    const context = match[0].toLowerCase();
    const delta =
      index === 0
        ? raw
        : /increase|rise|higher/.test(context)
          ? raw
          : -raw;
    return { deltaPct: delta, evidence: match[0].replace(/\s+/g, " ") };
  }
  const ratioMatches = [
    ...text.matchAll(/paired memory[^.\n]*?(?:ratio|geomean)[^.\n]*?`?(0?\.\d+)`?/gi),
  ];
  if (ratioMatches.length) {
    const match = ratioMatches[ratioMatches.length - 1];
    const ratio = Number(match[1]);
    return {
      deltaPct: (ratio - 1) * 100,
      evidence: match[0].replace(/\s+/g, " "),
    };
  }
  return null;
}

const methodOverrides = {
  1: "Watched CO-FR Event-Driven Shadow",
  2: "Watched CO-FR Event-Driven Shadow Repair",
  3: "Watched CO-FR Event-Driven Diagnostic",
  4: "First-Missing CO-FR Watch",
  5: "First-Missing CO-FR Profile",
  6: "Missing-Rule CO-FR Watch",
  7: "RF-Activation Watch",
  8: "RF-Activation 14-Task Gate",
  9: "Dynamic Watched-Closure Query",
  10: "Watched Callback Extraction",
  11: "Watched Callback Takeover",
  12: "Native Callback Ordering",
  13: "Native Callback Fallback",
  14: "Immediate Watched Callback",
  15: "Compact Watched Provenance",
  16: "Native Closure Row Skip",
  17: "Linear Reason Merge",
  18: "Repaired Linear Reason Merge",
  19: "CPU Hotspot Audit",
  20: "Clean Adaptive Residual Profile",
  21: "Native Packed Delta Shadow",
  22: "Native Packed Delta Takeover",
  23: "RF-First Branching",
  24: "Guarded RF Frontier",
  25: "Ranked RF-First Scheduling",
  26: "Batch Clause Minimization Opportunity",
  27: "Cached Clause Minimization Shadow",
  28: "Cached Clause Minimization Takeover",
  29: "Cached Clause Minimization",
  30: "Theory-Restart Epoch Scheduling",
  31: "Conjunctive Loop-Bound Inference",
  32: "Affine Loop-Bound Certificates",
  33: "Must-Assume Loop Bounds",
  34: "Existing Polynomial Loop Accelerator",
  35: "Interference-Stable Loop Normalization",
  36: "Concurrency k-Induction",
  38: "Event-Transparent Loop Summary",
  39: "Zero-Net-Effect Spinloop Summary",
  40: "Timeout Loop Taxonomy",
  41: "Nondeterministic Bulk Initialization",
  42: "Nondeterministic Bulk-Init Shadow",
  43: "Post-Initialization Weaver Loop Summary",
  44: "Shallow Counterexample Prepass",
  45: "Integrated Shallow Counterexample Prepass",
  49: "Interference-Closed Predicate Analysis Design",
  46: "Counterexample-Only Shallow Prepass",
  56: "Recursive-Worker Interference Fixed Point",
  57: "Loop-Contained Create Prefilter",
  69: "Multi-Template Worker Fixed Point",
  72: "Cost-Aware Multi-Template Scheduling",
  84: "Native Relational Fold",
  89: "Algebraic Segment Certificates",
  95: "Composite Loop Summaries",
  99: "Phase-Ordered Stream Cancellation",
  105: "Joined-Effect Summary",
  112: "Native JCES",
  122: "Prefix-Affine Envelope",
  126: "Ticket-Rank Serializability",
  127: "Concurrent Race Witness",
  128: "Lock Linearization Invariant",
  129: "CAS Linearization Stability",
  130: "Predicate-Stable Linearization",
  131: "Join-Scoped Transition-Word Equivalence",
  132: "Commuting Joined-Worker Sequentialization",
  133: "Lock-Ego Abstraction",
  134: "Monotone Helper Interference Audit",
  135: "Terminal Fresh-Array Loop Elimination",
  137: "Relational Extremum-Cone Invariant",
  138: "Extremum Homomorphism",
  139: "Loop Homomorphism",
  140: "Linear Recurrence Invariant",
  141: "Flow Recurrence Invariant",
  142: "Order Recurrence Invariant",
  143: "Hierarchical Stream Invariant",
  144: "Prefix-Language Channel Invariant",
  145: "Homogeneous Thread-Local Cutoff",
  146: "Finite Worker Cutoff",
  147: "Lock-Indexed Interval Invariant",
  148: "Modular Chunk Summary",
  157: "Property-Directed Affine Conservation",
  158: "Property-Directed Modular Lattice",
  159: "Modular-Lattice Timeout Theorem",
  160: "Role-Split Affine Stream",
  161: "Publication-Frontier Sequence Closure",
  162: "Join-Scoped Relational Bisimulation",
  163: "Join-Scoped Group-Action Cancellation",
  164: "Join-Scoped Segmented-Fold Conservation",
  165: "Join-Scoped Nested-Iteration Homomorphism",
  166: "Exact Local Counting-Loop Acceleration",
  167: "Monotone Counterexample Depth Portfolio",
  168: "Depth-4 Counterexample Portfolio",
  169: "Homogeneous Spawn Sequential Witness",
  170: "Guarded Alternating-Phase Recurrence",
  171: "Lifecycle-Guided Early Counterexample Prefix",
  172: "Large-Unwind Deferred Counterexample Rescue (unstable)",
  173: "Load-Robust Deferred Counterexample Rescue",
  174: "Dormant Symmetric-Thread Cutoff",
  175: "Conflict-Pair Dormant-Thread Decomposition",
  176: "Fork-After-Parse Native Portfolio",
  177: "Unified Native Counterexample Rescue",
  178: "Concurrency-Aware Property Slicing Prototype",
  179: "Spawn-Frontier Bulk Initialization",
  180: "Analysis-Preserving Deferred Bulk Initialization",
  181: "Residual Symbolic-Region Budget",
  182: "Mutex-Scoped Atomic Interference",
  183: "Predicate-Support Array Projection",
  184: "Index-Region Ownership",
  185: "Demand-Driven Stable Cells",
  186: "Post-Initialization Worker Recurrence Audit",
  187: "Protocol-Induced Capacity Cutoff",
  188: "Fused Protocol-Capacity Dispatch",
  189: "Abort-Aware Nested-Lock Relational Certificate",
  190: "Context-Instantiated Protected Regions",
  191: "Index-Correlated Protected Region Families",
  192: "Must-Pointer Congruence Digest",
  193: "Conditional Lock-Acquisition Transfer",
  194: "Container-Induced Dynamic Region Provenance",
  195: "Region-Lock Congruence Certificate",
  196: "Broad Event-Availability Guard Coherence",
  197: "Dynamic-Object Candidate Guard Coherence",
  198: "Multi-Target Dereference Guard Groups",
  199: "Conditional Event Generation",
  200: "Dynamic-Allocation Dereference Event Guards",
  201: "Guard-Conflict Read-From Pruning",
  202: "Latest Local Write RF Dominance",
  203: "Property-Relevant Concurrent Event Cone",
  204: "Synchronization-Relevance Closure Audit",
  205: "Residual Early-Stage Attribution",
  206: "Guarded Mutex-Region Fixed Point",
  207: "Interference-Closed WP Predicate Synthesis",
  208: "Property-Seeded WP Refinement",
  209: "WP Origin Proof-Core Attribution",
  210: "Controlled WP Seed-Origin Replication",
  211: "Cyclic-GOTO WP Refinement",
  212: "Property-Overlap GOTO WP Refinement",
  213: "Error-Control GOTO WP Refinement",
  214: "Error-Control WP Depth Minimization",
  215: "Error-Control Depth-2 Combined Natural Gate",
  216: "Relational Proof-Gap Audit",
  217: "Guarded Affine Transition Certificate",
  218: "Integrated Guarded Affine Dispatch",
  219: "Affine-Only Fail-Closed Dispatch Audit",
  220: "Delta-Cube Fixed-Point Worklist",
  221: "Post-Affine Combined Proof Dispatch",
  222: "Single-Process Combined Proof",
  223: "Typed Nondeterministic RHS Support",
  224: "Native-Atomic Affine Closure",
  225: "Finite-Constant Protocol Product",
  226: "Preprocessed Atomic Dispatch",
  227: "Weaver Residual Semantic Audit",
  228: "Large-Static Unwind Rescue",
  229: "libvsync Empty-Asm and Unwind Audit",
  230: "Remaining UNKNOWN/ERROR Mechanism Census",
  231: "Queue/Stack Large-Unwind Relation Audit",
  232: "Residual pthread-ext Mechanism Audit",
  233: "Ticket-Lock Ownership Certificate",
  234: "Structurally Dispatched Ticket Ownership",
  235: "Constant-Property Discharge Audit",
  236: "Mutex-State Call-Reachability Audit",
  237: "Lock-Allocated Index-Region Ownership",
  238: "Post-Store Stable-Cell Certificate",
  239: "Serialized Stack-Capacity Invariant",
  240: "Serialized Queue Sequence Correspondence",
  241: "Atomic Idempotent-Loop Commuting Sequentialization",
  242: "Large Static Complete-Unwind Admission Audit",
  243: "Nonnegative Oscillator Monitor",
  244: "Monotone Potential Overflow Audit",
  245: "Dynamic TLS Calloc-Zero Certificate",
  246: "TLS Destructor Counterexample Certificate",
  270: "Nested-Lifecycle Last-Writer Safety",
  271: "Boolean Atomic-Lock Region Safety",
  272: "Chunked Iterator Equivalence",
  273: "Poker-Hand Sequentialization",
  274: "Empty Compiler-Barrier Front End",
  275: "Work-Steal Queue Mutex Safety",
  276: "SafeStack ABA Counterexample",
  277: "Elimination-Backoff Counterexample",
  278: "libvsync Atomic Semantics",
  279: "Goblint Structural Race-Free Audit",
  280: "Linux Empty-Barrier Applicability",
  281: "Relational Comparator Antisymmetry",
  282: "Relational Comparator Transitivity",
  283: "Relational Comparator Substitution",
  284: "Unified Native Proof Portfolio",
  285: "Native Ticket Retry-Stuttering",
  286: "Single Pointer-Spin Collapse",
  287: "Pointer-Exception Scoped Spin Collapse",
  288: "Single-Worker Initialization Counterexample",
  289: "Shortened-Trace Projection Attempt",
  290: "Original-GOTO Guided Replay",
  291: "Prefix-Aware Retry Admission",
  292: "Native Residual Feasibility",
  293: "Affine and RF Selector Feasibility",
  294: "Native Modular Loop Summary",
  295: "Arbitrary-Initial Local Clamp Acceleration",
  296: "Bounded Alternating Cancellation",
};

const statusOverrides = {
  1: "failed",
  2: "audit",
  3: "failed",
  4: "audit",
  5: "audit",
  6: "audit",
  7: "audit",
  8: "audit",
  9: "audit",
  10: "audit",
  11: "audit",
  12: "audit",
  13: "audit",
  14: "audit",
  15: "audit",
  16: "audit",
  17: "failed",
  18: "failed",
  19: "audit",
  20: "audit",
  29: "failed",
  30: "failed",
  31: "failed",
  32: "failed",
  33: "failed",
  34: "failed",
  35: "failed",
  36: "failed",
  38: "failed",
  39: "failed",
  40: "audit",
  41: "audit",
  42: "failed",
  43: "failed",
  44: "audit",
  45: "audit",
  46: "successful",
  49: "audit",
  56: "successful",
  59: "audit",
  60: "audit",
  72: "audit",
  82: "failed",
  83: "failed",
  84: "successful",
  89: "successful",
  94: "audit",
  95: "successful",
  99: "successful",
  100: "successful",
  105: "successful",
  110: "failed",
  112: "successful",
  122: "successful",
  126: "successful",
  127: "successful",
  128: "successful",
  129: "successful",
  130: "successful",
  131: "successful",
  132: "successful",
  133: "successful",
  134: "audit",
  135: "successful",
  136: "audit",
  137: "successful",
  138: "successful",
  139: "successful",
  140: "successful",
  141: "successful",
  142: "successful",
  143: "successful",
  144: "successful",
  145: "successful",
  146: "successful",
  147: "successful",
  148: "failed",
  149: "failed",
  150: "failed",
  151: "audit",
  152: "failed",
  153: "failed",
  154: "audit",
  155: "audit",
  156: "audit",
  157: "successful",
  158: "successful",
  159: "successful",
  160: "successful",
  161: "successful",
  162: "successful",
  163: "successful",
  164: "successful",
  165: "successful",
  166: "successful",
  167: "successful",
  168: "failed",
  169: "successful",
  170: "successful",
  171: "successful",
  172: "failed",
  173: "successful",
  174: "successful",
  175: "successful",
  176: "successful",
  177: "successful",
  178: "failed",
  179: "failed",
  180: "failed",
  181: "successful",
  182: "failed",
  183: "failed",
  184: "failed",
  185: "failed",
  186: "audit",
  187: "successful",
  188: "successful",
  189: "successful",
  190: "successful",
  191: "successful",
  192: "successful",
  193: "successful",
  194: "successful",
  195: "successful",
  196: "failed",
  197: "failed",
  198: "failed",
  199: "failed",
  200: "failed",
  201: "failed",
  202: "failed",
  203: "successful",
  204: "failed",
  205: "audit",
  206: "failed",
  207: "failed",
  208: "failed",
  209: "failed",
  210: "failed",
  211: "failed",
  212: "failed",
  213: "failed",
  214: "failed",
  215: "failed",
  216: "audit",
  217: "successful",
  218: "successful",
  219: "failed",
  220: "failed",
  221: "successful",
  222: "successful",
  223: "failed",
  224: "failed",
  225: "failed",
  226: "successful",
  227: "failed",
  228: "failed",
  229: "failed",
  230: "failed",
  231: "failed",
  232: "failed",
  233: "failed",
  234: "successful",
  235: "failed",
  236: "failed",
  237: "successful",
  238: "successful",
  239: "successful",
  240: "successful",
  241: "failed",
  242: "failed",
  243: "successful",
  244: "failed",
  245: "successful",
  246: "successful",
  247: "successful",
  248: "successful",
  249: "successful",
  250: "successful",
  251: "successful",
  252: "successful",
  253: "successful",
  254: "successful",
  255: "failed",
  256: "successful",
  257: "successful",
  258: "successful",
  259: "successful",
  260: "successful",
  261: "successful",
  262: "successful",
  263: "successful",
  264: "failed",
  265: "failed",
  266: "successful",
  267: "successful",
  268: "successful",
  269: "failed",
  270: "successful",
  271: "successful",
  272: "failed",
  273: "failed",
  274: "failed",
  275: "failed",
  276: "failed",
  277: "failed",
  278: "failed",
  279: "failed",
  280: "failed",
  281: "successful",
  282: "successful",
  283: "successful",
  284: "successful",
  285: "successful",
  286: "failed",
  287: "successful",
  288: "successful",
  289: "failed",
  290: "successful",
  291: "successful",
  292: "failed",
  293: "failed",
  294: "successful",
  295: "successful",
  296: "successful",
};

// These versions changed only the Python wrapper and left the production C++
// and native deagle_exe byte-identical. Preserve their raw portfolio results,
// but do not count them as verifier contributions until native redo passes.
const wrapperOnlyVersions = new Set();
const wrapperEvidenceVersions = new Set([
  256, 257, 258, 259, 260, 261, 262, 263,
]);
const nativeRedoVersions = new Set([
  256, 257, 258, 259, 260, 261, 262, 263, 266, 267, 268, 270, 271,
  281, 282, 283, 284, 285, 286, 287, 288, 289, 290, 291, 294, 295,
  296,
]);
const nativeRedoMemorySources = {
  256: "/data3/sujie/experiments/native-redo-v256-v263-20260728/v256/full-v256-native-depth-results/full-v256-native.2026-07-27_17-26-19.results.v255-conserved-sum.Concurrency.xml.bz2",
  257: "/data3/sujie/experiments/native-redo-v256-v263-20260728/v256/full-v256-native-depth-results/full-v256-native.2026-07-27_17-26-19.results.v255-conserved-sum.Concurrency.xml.bz2",
  258: "../../experiments/native-redo-v256-v263-20260728/v258/full-v258-native-results/full-v258-native.2026-07-27_18-48-35.results.v255-conserved-sum.Concurrency.xml.bz2",
  259: "../../experiments/native-redo-v256-v263-20260728/v259/full-v259-native-results/full-v259-native.2026-07-28_03-42-12.results.v255-conserved-sum.Concurrency.xml.bz2",
  260: "/data3/sujie/experiments/native-redo-v256-v263-20260728/v260/full-v260-native-results/full-v260-native.2026-07-28_04-10-03.results.v255-conserved-sum.Concurrency.xml.bz2",
  261: "/data3/sujie/experiments/native-redo-v256-v263-20260728/v261/full-v261-native-results/full-v261-native.2026-07-28_04-27-08.results.v255-conserved-sum.Concurrency.xml.bz2",
  262: "/data3/sujie/experiments/native-redo-v256-v263-20260728/v262/full-v262-ubfix-results/full-v262-native.2026-07-28_04-48-01.results.v255-conserved-sum.Concurrency.xml.bz2",
  263: "/data3/sujie/experiments/native-redo-v256-v263-20260728/v263/full-v263-native-real-results/full-v263-native.2026-07-28_05-29-02.results.v255-conserved-sum.Concurrency.xml.bz2",
  266: "/data3/sujie/experiments/mutex-zero-fixedpoint-safety-v266-20260728/full-v266-results/full-v266.2026-07-28_06-25-56.results.v266-mutex-zero-fixedpoint.Concurrency.xml.bz2",
  267: "../../experiments/singleton-function-pointer-zero-sum-v267-20260728/full-v267.xml.bz2",
  268: "../../experiments/indexed-lock-zero-sum-v268-20260728/full-v268.xml.bz2",
  270: "../../experiments/nested-lifecycle-last-writer-safety-v270-20260728/full-v270-result.xml.bz2",
  271: "../../experiments/boolean-atomic-lock-region-safety-v271-20260728/full-v271-result.xml.bz2",
  281: "../../experiments/relational-comparator-certificate-v281-20260728/artifacts/full-v281.2026-07-28_14-18-20.results.v281-relational-comparator-certificate.Concurrency.xml.bz2",
  282: "../../experiments/relational-comparator-transitivity-v282-20260728/artifacts/full-v282.2026-07-28_15-37-06.results.v282-relational-comparator-transitivity.Concurrency.xml.bz2",
  283: "/data3/sujie/experiments/accepted-optimization-git-integration-20260728/exact725-v283-r40/exact725.2026-07-28_21-25-48.results.accepted-native-integration-exact725.Concurrency.xml.bz2",
  284: "/data3/sujie/experiments/v284-unified-exact725-r5/results/exact725.2026-07-29_06-24-17.results.accepted-native-integration-exact725.Concurrency.xml.bz2",
  285: "/data3/sujie/experiments/v285-ticket-native-final-exact725-r1/results/exact725.2026-07-29_09-44-02.results.accepted-native-integration-exact725.Concurrency.xml.bz2",
  286: "/data3/sujie/experiments/v286-single-pointer-spin-exact725-r1/results/exact725.2026-07-29_12-35-01.results.accepted-native-integration-exact725.Concurrency.xml.bz2",
  287: "/data3/sujie/experiments/v287-pointer-exception-scope-exact725-r1/results/exact725.2026-07-29_12-55-14.results.accepted-native-integration-exact725.Concurrency.xml.bz2",
  288: "/data3/sujie/experiments/v288-native-single-worker-exact725-r1/results/exact725.2026-07-29_13-34-25.results.accepted-native-integration-exact725.Concurrency.xml.bz2",
  289: "/data3/sujie/experiments/v289-evilcollapse-exact725-r1/results/exact725.2026-07-29_14-32-37.results.accepted-native-integration-exact725.Concurrency.xml.bz2",
  290: "/data3/sujie/experiments/v290-original-goto-replay-exact725-r2/results/exact725.2026-07-29_18-15-31.results.accepted-native-integration-exact725.Concurrency.xml.bz2",
  291: "/home/lapulatos/deagle-experiments/v291-exact725-r1/results-n8exact725.server.2026-07-30_03-09-49.results.v291-native-prefix-reachability-exact725.Concurrency.xml.bz2",
  294: "/home/lapulatos/deagle-experiments/v294-paired-candidate-exact725-r1/results/exact725.server.2026-07-30_04-41-12.results.v294-native-modular-loop-exact725.Concurrency.xml.bz2",
  295: "/home/lapulatos/deagle-experiments/v295-paired-candidate-exact725-r1/resultsexact725.server.2026-07-30_05-08-14.results.v295-native-local-clamp-exact725.Concurrency.xml.bz2",
  296: "/home/lapulatos/deagle-experiments/v296-paired-candidate-exact725-r1/results/exact725.server.2026-07-30_05-31-16.results.v296-native-bounded-alternating-exact725.Concurrency.xml.bz2",
};
const wrapperMetricOverrides = {
  256: {
    correct: 684,
    cpu_s: 1204.4573272090006,
    wall_s: 1233.4285293414723,
    memory_sum_b: 24467214336,
  },
  257: {
    correct: 685,
    cpu_s: 1207.4749497639991,
    wall_s: 1236.6958920054603,
    memory_sum_b: 24502198272,
  },
  258: {
    correct: 686,
    cpu_s: 1208.065720532,
    wall_s: 1237.4091860022163,
    memory_sum_b: 24514752512,
  },
  259: {
    correct: 687,
    cpu_s: 1215.256050987,
    wall_s: 1243.8744210188743,
    memory_sum_b: 24574001152,
  },
  260: {
    correct: 688,
    cpu_s: 1214.183022833,
    wall_s: 1243.5545231355354,
    memory_sum_b: 24667418624,
  },
  261: {
    correct: 689,
    cpu_s: 1224.081985708,
    wall_s: 1253.1376563977683,
    memory_sum_b: 24465362944,
  },
  262: {
    correct: 690,
    cpu_s: 1227.160429512,
    wall_s: 1255.7690372487996,
    memory_sum_b: 24557170688,
  },
  263: {
    correct: 691,
    cpu_s: 1164.09645089,
    wall_s: 1193.1416233569616,
    memory_sum_b: 24674693120,
  },
};

const exactOverrides = {
  0: { correct: 444, cpu: 12737.303, wall: 12762.179, peak: 3999997952 },
  29: { correct: 444, cpu: 12707.903, wall: 12731.129, peak: 3999997952 },
  46: { correct: 460, cpu: 11761.158, wall: 11787.863, peak: 3999997952 },
  56: { correct: 462, cpu: 11174.783, wall: 12039.904, peak: 3999997952 },
  59: { correct: 462, cpu: 11639.443, wall: 11668.661, peak: 3999997952 },
  69: { correct: 464, cpu: 11547.367, wall: 11576.159, peak: 3999997952 },
  72: { correct: 464, cpu: 11540.239, wall: 11574.964, peak: 3999997952 },
  82: { correct: 474, cpu: 10955.735, wall: 10986.572, peak: 3999997952 },
  83: { correct: 474, cpu: 10949.734, wall: 10984.914, peak: 3999997952 },
  84: { correct: 474, cpu: 10936.837925558, wall: 10968.347739661, peak: 3999997952 },
  89: { correct: 481, cpu: 10506.757471286, wall: 10541.448344443, peak: 3999997952 },
  95: { correct: 484, cpu: 10326.648, wall: 10358.443, peak: 3999997952 },
  99: { correct: 488, cpu: 10082.093, wall: 10113.262, peak: 3999997952 },
  105: { correct: 497, cpu: 9527.519156369, wall: 9787.19079449505, peak: 3999997952 },
  110: { correct: 502, cpu: 9224.029552, wall: 9521.241465, peak: 3999997952 },
  112: { correct: 503, cpu: 9168.254086, wall: 9467.964007, peak: 3999997952 },
  122: { correct: 504, cpu: 9029.505, wall: 9315.012, peak: 3999997952 },
  126: { correct: 508, cpu: 8765.685, wall: 8810.449, peak: 3999998000 },
  127: { correct: 509, cpu: 8709.699, wall: 8750.722, peak: 3999998000 },
  128: { correct: 511, cpu: 8580.254, wall: 8622.397, peak: 3999998000 },
  129: { correct: 513, cpu: 8459.057, wall: 8644.793, peak: 4000000000 },
  130: { correct: 521, cpu: 7978.895, wall: 8006.758, peak: 4000000000 },
  131: { correct: 525, cpu: 7737.442, wall: 7763.987, peak: 4000000000 },
  132: { correct: 531, cpu: 7371.721, wall: 7398.7, peak: 4000000000 },
  133: { correct: 532, cpu: 7309.698, wall: 7338.148, peak: 4000000000 },
  135: { correct: 535, cpu: 7125.629, wall: 7158.9, peak: 4000000000 },
  137: { correct: 544, cpu: 6581.818, wall: 6608.522, peak: 4000000000 },
  138: { correct: 546, cpu: 6470.318, wall: 6495.869, peak: 4000000000 },
  139: { correct: 549, cpu: 6288.174, wall: 6313.816, peak: 4000000000 },
  140: { correct: 554, cpu: 5987.638, wall: 6012.823, peak: 4000000000 },
  141: { correct: 559, cpu: 5681.89, wall: 5704.85, peak: 4000000000 },
  142: { correct: 562, cpu: 5501.335, wall: 5524.246, peak: 4000000000 },
  143: { correct: 567, cpu: 5196.295, wall: 5219.786, peak: 4000000000 },
  144: { correct: 573, cpu: 4828.972, wall: 4852.496, peak: 4000000000 },
  145: { correct: 575, cpu: 4710.886, wall: 4733.318, peak: 4000000000 },
  146: { correct: 579, cpu: 4469.877, wall: 4494.185, peak: 4000000000 },
  147: { correct: 581, cpu: 4348.536, wall: 4371.967, peak: 4000000000 },
  148: { correct: 585, cpu: 4057.17, wall: 4080.037, peak: 3999998000 },
  157: { correct: 582, cpu: 4225.837, wall: 4248.684, peak: 4000000000 },
  158: { correct: 583, cpu: 4226.127, wall: 4247.663, peak: 4000000000 },
  159: { correct: 585, cpu: 4042.771, wall: 4064.731, peak: 4000000000 },
  160: { correct: 588, cpu: 3922.85, wall: 3943.106, peak: 3999997952 },
  161: { correct: 592, cpu: 3613.627, wall: 3634.552, peak: 3999997952 },
  162: { correct: 594, cpu: 3560.427, wall: 3583.175, peak: 3999997952 },
  163: { correct: 596, cpu: 3513.025, wall: 3526.737, peak: 3999633408 },
  164: { correct: 597, cpu: 3455.951, wall: 3469.396, peak: 3999629312 },
  165: { correct: 598, cpu: 3400.611, wall: 3414.563, peak: 3999612928 },
  166: { correct: 600, cpu: 3281.476, wall: 3294.791, peak: 3999625216 },
  167: { correct: 604, cpu: 3044.731, wall: 3070.712, peak: 3999997952 },
  169: { correct: 605, cpu: 2980.453, wall: 3006.475, peak: 3999997952 },
  170: { correct: 606, cpu: 2921.189, wall: 2946.594, peak: 3999997952 },
  171: { correct: 608, cpu: 2810.353, wall: 2837.948, peak: 3999997952 },
  172: { correct: 611, cpu: 2989.724, wall: 3021.21, peak: 3999997952 },
  173: { correct: 612, cpu: 2935.134, wall: 2966.363, peak: 3999997952 },
  174: { correct: 625, cpu: 2954.771, wall: 2985.56, peak: 3999997952 },
  175: { correct: 630, cpu: 2986.936, wall: 3019.037, peak: 3999997952 },
  176: { correct: 630, cpu: 2905.327, wall: 2939.302, peak: 3999997952 },
  177: { correct: 630, cpu: 2897.049, wall: 2929.58, peak: 3999997952 },
  180: { correct: 630, cpu: 2891.99, wall: 2925.315, peak: 3999997952 },
  181: { correct: 631, cpu: 2836.669, wall: 2868.463, peak: 3999997952 },
  187: { correct: 635, cpu: 2651.614797628, wall: 2702.8493496570736, peak: 3999997952 },
  188: { correct: 635, cpu: 2592.137512974, wall: 2623.1753125234973, peak: 3999997952 },
  189: { correct: 637, cpu: 2589.151891558, wall: 2620.292000974994, peak: 3999997952 },
  190: { correct: 641, cpu: 2575.998098589, wall: 2606.548923523864, peak: 3999997952 },
  191: { correct: 646, cpu: 2574.652955357001, wall: 2605.069153071614, peak: 3999997952 },
  192: { correct: 648, cpu: 2573.498902392001, wall: 2604.006005124189, peak: 3999997952 },
  193: { correct: 650, cpu: 2570.9563300149953, wall: 2601.458520903485, peak: 3999997952 },
  194: { correct: 652, cpu: 2562.108056541999, wall: 2590.975206524832, peak: 3999997952 },
  195: { correct: 652, cpu: 2564.269124301001, wall: 2594.7453050420154, peak: 3999997952 },
  196: { correct: 648, cpu: 2744.48038766, wall: 2772.914761819644, peak: 3999997952 },
  197: { correct: 651, cpu: 2697.993791595, wall: 2725.744948232197, peak: 3999997952 },
  199: { correct: 651, cpu: 2699.786823212, wall: 2728.2076069434406, peak: 3999997952 },
  200: { correct: 651, cpu: 2609.548366901, wall: 2639.3167088910704, peak: 3999997952 },
  203: { correct: 652, cpu: 2507.050019702, wall: 2537.199433997, peak: 3999997952 },
  217: { correct: 655, cpu: 2398.9619804769977, wall: 2429.3490511418786, peak: 3999997952 },
  218: { correct: 655, cpu: 2331.5011063990005, wall: 2362.812985364115, peak: 3999997952 },
  220: { correct: 655, cpu: 2334.55347143, wall: 2365.792302465299, peak: 3999997952 },
  221: { correct: 657, cpu: 2214.72797363, wall: 2246.6477038895246, peak: 3999997952 },
  222: { correct: 657, cpu: 2214.670303445, wall: 2246.3932147194864, peak: 3999997952 },
  225: { correct: 657, cpu: 2275.044592594, wall: 2304.927760864375, peak: 3999997952 },
  226: { correct: 660, cpu: 2088.109734479, wall: 2118.2589659522055, peak: 3999997952 },
  233: { correct: 661, cpu: 2017.290621126, wall: 2047.9121288815513, peak: 3999997952 },
  234: { correct: 662, cpu: 1963.809157165, wall: 1994.8034674422815, peak: 3999997952 },
  237: { correct: 664, cpu: 1848.7006519090003, wall: 1878.6482470136834, peak: 3999997952 },
  238: { correct: 666, cpu: 1728.197979525, wall: 1757.655124468496, peak: 3999997952 },
  239: { correct: 668, cpu: 1717.407047352, wall: 1747.2697022235952, peak: 3999997952 },
  240: { correct: 670, cpu: 1709.147737256, wall: 1739.520209371578, peak: 3999997952 },
  241: { correct: 670, cpu: 1709.147737256, wall: 1739.520209371578, peak: 3999997952 },
  242: { correct: 670, cpu: 1709.147737256, wall: 1739.520209371578, peak: 3999997952 },
  243: { correct: 671, cpu: 1655.989678153, wall: 1686.4829210561002, peak: 3999997952 },
  244: { correct: 671, cpu: 1655.989678153, wall: 1686.4829210561002, peak: 3999997952 },
  245: { correct: 672, cpu: 1598.747031391, wall: 1629.126979312161, peak: 3999997952 },
  246: { correct: 673, cpu: 1598.872494703, wall: 1629.326790784602, peak: 3999997952 },
  247: { correct: 674, cpu: 1603.095127337, wall: 1633.377046019421, peak: 3999997952 },
  248: { correct: 675, cpu: 1547.515635386, wall: 1577.4903934490867, peak: 3999997952 },
  249: { correct: 676, cpu: 1494.787371362, wall: 1524.5379580240697, peak: 3999997952 },
  250: { correct: 677, cpu: 1438.993138961, wall: 1469.1238685994176, peak: 3999997952 },
  251: { correct: 678, cpu: 1381.278470579, wall: 1414.290667127585, peak: 3999997952 },
  252: { correct: 679, cpu: 1323.6970582230006, wall: 1353.9723155956017, peak: 3999997952 },
  253: { correct: 680, cpu: 1264.8053403299996, wall: 1294.9803815060295, peak: 3999997952 },
  254: { correct: 681, cpu: 1203.4617203379987, wall: 1233.667673881282, peak: 3999997952 },
  256: { correct: 684, cpu: 1174.583025949, wall: 1200.549746716977, peak: 3999997952 },
  257: { correct: 684, cpu: 1174.583025949, wall: 1200.549746716977, peak: 3999997952 },
  258: { correct: 685, cpu: 1227.181420144, wall: 1256.8216319811763, peak: 3999997952 },
  259: { correct: 686, cpu: 1175.713834218, wall: 1197.3521209484898, peak: 3999997952 },
  260: { correct: 687, cpu: 1178.834081838, wall: 1201.4165163246216, peak: 3999997952 },
  261: { correct: 688, cpu: 1181.942264104, wall: 1204.2129293229664, peak: 3999997952 },
  262: { correct: 689, cpu: 1189.129119127, wall: 1211.324997216463, peak: 3999997952 },
  263: { correct: 690, cpu: 1250.195763952, wall: 1290.9734508773545, peak: 3999997952 },
  266: { correct: 691, cpu: 1256.417101767, wall: 1296.6684456527, peak: 3999997952 },
  267: { correct: 693, cpu: 1136.34285141, wall: 1175.9259267748566, peak: 3999997952 },
  268: { correct: 694, cpu: 1034.871633912, wall: 1063.7983498902759, peak: 3999997952 },
  270: { correct: 695, cpu: 1068.617481672, wall: 1109.139516892843, peak: 3999997952 },
  271: { correct: 696, cpu: 1003.271697325, wall: 1043.430507744895, peak: 3999997952 },
  281: { correct: 697, cpu: 946.604792418, wall: 986.5009775378, peak: 3999997952 },
  282: { correct: 698, cpu: 883.906323, wall: 924.530255, peak: 3999997952 },
  283: { correct: 698, cpu: 919.289765, wall: 953.451938, peak: 3999997952 },
  284: { correct: 699, cpu: 859.041804128, wall: 903.4940643096343, peak: 3999997952 },
  285: { correct: 700, cpu: 861.356850191, wall: 906.056512353, peak: 3999997952 },
  286: { correct: 700, cpu: 871.2369108290002, wall: 915.1920141403098, peak: 3999997952 },
  287: { correct: 701, cpu: 866.534168323, wall: 910.8745472538285, peak: 3999997952 },
  288: { correct: 701, cpu: 865.0478599520001, wall: 908.7999609876424, peak: 3999997952 },
  289: { correct: 701, cpu: 948.0651588590009, wall: 984.282939416822, peak: 3999641600 },
  290: { correct: 701, cpu: 894.0097913300003, wall: 938.8530091892462, peak: 3999997952 },
  291: { correct: 693, cpu: 1383.8831540000003, wall: 1421.6679298453964, peak: 3999997952 },
  294: { correct: 696, cpu: 1206.378017999999, wall: 1247.4008251582272, peak: 3999997952 },
  295: { correct: 697, cpu: 1146.603572, wall: 1187.2987553104758, peak: 3999997952 },
  296: { correct: 698, cpu: 1093.065036, wall: 1134.9193168370984, peak: 3999997952 },
};

// The public YAML for task82 is mechanically derived from a Goblint UNKNOWN
// annotation. Manual pthread-semantics adjudication treats TRUE as correct.
// Keep exactOverrides as the official XML tuple for provenance matching and
// expose the adjudicated correct count in the dashboard.
const adjudicatedCorrectOverrides = {
  194: 653,
  196: 649,
  197: 652,
  199: 652,
  200: 652,
  203: 653,
  217: 656,
  218: 656,
  220: 656,
  221: 658,
  222: 658,
  225: 658,
  226: 661,
  233: 662,
  234: 663,
  237: 665,
  238: 667,
  239: 669,
  240: 671,
  241: 671,
  242: 671,
  243: 672,
  244: 672,
  245: 673,
  246: 674,
  247: 675,
  248: 676,
  249: 677,
  250: 678,
  251: 679,
  252: 680,
  253: 681,
  254: 682,
  256: 685,
  257: 685,
  258: 686,
  259: 687,
  260: 688,
  261: 689,
  262: 690,
  263: 691,
  266: 692,
  267: 694,
  268: 695,
  270: 696,
  271: 697,
  281: 698,
  282: 699,
  283: 699,
  284: 700,
  285: 701,
  286: 701,
  287: 702,
  288: 703,
  289: 703,
  290: 704,
  291: 705,
  294: 708,
  295: 709,
  296: 710,
};

// Sum of BenchExec's per-task `memory` column over all 725 tasks. These values
// were recomputed directly from the preserved XML files on the experiment
// server. They are intentionally separate from `peak`, which is only the
// maximum memory of one task and is not a full-suite resource total.
const memorySumOverrides = {
  0: 68299001856,
  29: 67956215808,
  46: 68226453504,
  56: 66480758784,
  59: 67978014720,
  69: 63791366144,
  72: 63707824128,
  82: 65449635840,
  83: 61722783744,
  84: 61851742208,
  89: 60167909376,
  95: 59424276480,
  99: 58278821888,
  105: 55308947456,
  110: 53717577728,
  112: 53660835840,
  122: 52818817024,
  126: 52494516224,
  127: 51979509760,
  128: 51602165760,
  129: 51860066304,
  130: 48462123008,
  131: 47518035968,
  132: 46204276736,
  133: 46217703424,
  135: 45787471872,
  137: 42879021056,
  138: 42448961536,
  139: 42234646528,
  140: 40017129472,
  141: 38660591616,
  142: 37951606784,
  143: 36548079616,
  144: 34976636928,
  145: 34856558592,
  146: 34664058880,
  147: 33971896320,
  148: 32307486720,
  157: 34050801664,
  158: 33602011136,
  159: 33466933248,
  160: 32277499904,
  161: 31182061568,
  162: 31127453696,
  163: 30197411840,
  164: 30118232064,
  165: 29604675584,
  166: 28049362944,
  167: 25669898240,
  169: 25601200128,
  170: 25483997184,
  171: 25696157696,
  172: 34186579968,
  173: 34043596800,
  174: 38706970624,
  175: 40620834816,
  176: 39998967808,
  177: 40017920000,
  180: 38787346432,
  181: 39589552128,
  187: 38479290368,
  188: 38384365568,
  189: 37742215168,
  190: 35703984128,
  191: 35704438784,
  192: 35078737920,
  193: 34302844928,
  194: 33770532864,
  195: 33926967296,
  196: 33788190720,
  197: 33622917120,
  199: 33674092544,
  200: 33739116544,
  203: 26844622848,
  217: 29535916032,
  218: 26734747648,
  220: 26732269568,
  221: 26623918080,
  222: 26560638976,
  225: 26571001856,
  226: 26072727552,
  233: 25765847040,
  234: 26248269824,
  237: 26592956416,
  238: 26244182016,
  239: 25972404224,
  240: 24954265600,
  241: 24954265600,
  242: 24954265600,
  243: 24991068160,
  244: 24991068160,
  245: 25394925568,
  246: 25456803840,
  247: 25774977024,
  248: 25715171328,
  249: 25680318464,
  250: 25627951104,
  251: 25679564800,
  252: 25302093824,
  253: 25216737280,
  254: 24696680448,
  256: 25778589696,
  257: 25778589696,
  258: 25570484224,
  259: 26466152448,
  260: 26873638912,
  261: 26563518464,
  262: 26724327424,
  263: 27473588224,
  266: 27706974208,
  267: 27560644608,
  268: 27592212480,
  270: 27364478976,
  271: 27290218496,
  281: 27215429632,
  282: 26961915904,
  283: 25604014080,
  284: 25426169856,
  285: 25645174784,
  286: 25666789376,
  287: 25625346048,
  288: 25715208192,
  289: 25412145152,
  290: 26493808640,
  291: 28949061632,
  294: 28088336384,
  295: 27623301120,
  296: 27417141248,
};

// Paired-memory reporting used several textual forms that are unsafe to parse
// generically (ratios, percentages, and control/method table cells). Keep the
// comparable geometric-mean deltas explicit and leave genuinely absent values
// null.
const memoryDeltaOverrides = {
  0: 0,
  29: 0.05,
  46: -2.915,
  56: -1.51,
  59: 0.001,
  69: -0.789,
  72: 0.232,
  82: 20.13,
  83: -4.69,
  84: -3.288,
  89: -3.186,
  99: -1.99,
  105: -3.55,
  110: -2.42,
  112: -2.52,
  122: -1.5,
  126: -0.45,
  127: -0.47,
  128: -0.78,
  129: -0.44,
  130: -3.7,
  131: -1.57,
  133: 0.24,
  137: -2.24,
  138: -0.765,
  139: -1.172,
  140: -2.11,
  141: -2.02,
  142: -1.19,
  143: -1.935,
  144: -2.452,
  145: -0.57,
  146: -1.16,
  147: -0.87,
  157: -0.123,
  158: -0.59,
  159: -0.65,
  161: -1.592,
  173: 7.5,
};

const directoriesByVersion = new Map();
for (const directory of fs.readdirSync(recordsRoot)) {
  const full = path.join(recordsRoot, directory);
  if (!fs.statSync(full).isDirectory()) continue;
  const version = lastVersion(directory);
  if (version === null || version < 1 || version > 296) continue;
  if (!directoriesByVersion.has(version)) directoriesByVersion.set(version, []);
  directoriesByVersion.get(version).push(directory);
}
const localExperimentsRoots = [
  path.join(repoRoot, "experiments"),
  process.env.DEAGLE_SUPPLEMENTAL_EXPERIMENTS_ROOT,
].filter(
  (directory, index, roots) =>
    directory &&
    fs.existsSync(directory) &&
    roots.indexOf(directory) === index
);
for (const localExperimentsRoot of localExperimentsRoots) {
  for (const directory of fs.readdirSync(localExperimentsRoot)) {
    const full = path.join(localExperimentsRoot, directory);
    if (!fs.statSync(full).isDirectory()) continue;
    const version = lastVersion(directory);
    if (version === null || version < 1 || version > 296) continue;
    if (!directoriesByVersion.has(version))
      directoriesByVersion.set(version, []);
    if (!directoriesByVersion.get(version).includes(directory))
      directoriesByVersion.get(version).push(directory);
  }
}

// V1 predates the consistent version suffix. V17--V20 were recorded in the
// shared project-state note rather than in separate experiment directories.
directoriesByVersion.set(1, ["watched-cofr-event-driven-shadow-20260722"]);
const projectStateDirectory = "shallow-prepass-trigger-v47-20260723";
for (const version of [17, 18, 19, 20])
  directoriesByVersion.set(version, [projectStateDirectory]);
directoriesByVersion.set(49, ["goto-ir-admission-v52-20260723"]);
directoriesByVersion.set(168, [
  "homogeneous-spawn-sequential-witness-v169-20260726",
]);
directoriesByVersion.set(233, [
  "ticket-lock-ownership-v233-20260727",
]);
directoriesByVersion.set(234, [
  "ticket-lock-dispatch-v234-20260727",
]);
directoriesByVersion.set(235, [
  "constant-property-discharge-v235-20260727",
]);
directoriesByVersion.set(236, [
  "mutex-state-call-reachability-v236-20260727",
]);
directoriesByVersion.set(237, [
  "index-region-ownership-v237-20260727",
]);
directoriesByVersion.set(238, [
  "post-store-stable-cell-v238-20260727",
]);
directoriesByVersion.set(239, [
  "stack-capacity-invariant-v239-20260727",
]);
directoriesByVersion.set(240, [
  "queue-sequence-correspondence-v240-20260727",
]);
directoriesByVersion.set(241, [
  "readonly-comparator-algebra-v241-20260727",
]);
directoriesByVersion.set(242, [
  "large-static-complete-unwind-v242-20260727",
]);
directoriesByVersion.set(243, [
  "nonnegative-oscillator-monitor-v243-20260727",
]);
directoriesByVersion.set(244, [
  "monotone-potential-overflow-audit-v244-20260727",
]);
directoriesByVersion.set(245, [
  "dynamic-tls-calloc-zero-v245-20260727",
]);
directoriesByVersion.set(246, [
  "tls-destructor-counterexample-v246-20260727",
]);
directoriesByVersion.set(247, [
  "partitioned-count-reduction-v247-20260727",
]);
directoriesByVersion.set(248, [
  "finite-two-sided-disjunction-v248-20260727",
]);
directoriesByVersion.set(249, [
  "completion-flag-arithmetic-v249-20260727",
]);
directoriesByVersion.set(250, [
  "nonzero-cas-seed-v250-20260727",
]);
directoriesByVersion.set(251, [
  "monotone-chunk-maximum-v251-20260727",
]);
directoriesByVersion.set(252, [
  "linear-tiled-copy-equivalence-v252-20260727",
]);
directoriesByVersion.set(253, [
  "atomic-queue-occupancy-value-v253-20260727",
]);
directoriesByVersion.set(254, [
  "isomorphic-modular-fold-pair-v254-20260727",
]);
directoriesByVersion.set(255, [
  "conserved-sum-nontermination-v255-20260727",
]);
directoriesByVersion.set(256, [
  "encoded-race-counterexample-v256-20260727",
]);
directoriesByVersion.set(257, [
  "misaligned-index-lock-counterexample-v257-20260727",
]);
directoriesByVersion.set(258, [
  "same-slot-different-lock-counterexample-v258-20260727",
]);
directoriesByVersion.set(259, [
  "cross-slot-list-splice-counterexample-v259-20260727",
]);
directoriesByVersion.set(260, [
  "independent-object-lock-index-counterexample-v260-20260727",
]);
directoriesByVersion.set(261, [
  "wrapped-mutex-zero-sum-safety-v261-20260727",
]);
directoriesByVersion.set(262, [
  "guard-dominated-common-mutex-safety-v262-20260727",
]);
directoriesByVersion.set(263, [
  "monotone-condition-wait-safety-v263-20260728",
]);
directoriesByVersion.set(264, [
  "explicit-boolean-lock-protocol-safety-v264-20260728",
]);
directoriesByVersion.set(265, [
  "unwind-progress-logging-demotion-v265-20260728",
]);
directoriesByVersion.set(266, [
  "mutex-zero-fixedpoint-safety-v266-20260728",
]);
directoriesByVersion.set(269, [
  "indexed-list-race-safety-v269-20260728",
]);
directoriesByVersion.set(270, [
  "nested-lifecycle-last-writer-safety-v270-20260728",
]);
directoriesByVersion.set(271, [
  "boolean-atomic-lock-region-safety-v271-20260728",
]);
directoriesByVersion.set(272, [
  "chunked-iterator-equivalence-v272-20260728",
]);
directoriesByVersion.set(273, [
  "poker-hand-equivalence-v273-20260728",
]);
directoriesByVersion.set(274, [
  "empty-compiler-barrier-v274-20260728",
]);
directoriesByVersion.set(275, [
  "workstealqueue-mutex-safety-v275-20260728",
]);
directoriesByVersion.set(276, [
  "safestack-relacy-counterexample-v276-20260728",
]);
directoriesByVersion.set(277, [
  "elimination-backoff-native-v277-20260728",
]);
directoriesByVersion.set(278, [
  "libvsync-atomic-semantics-v278-20260728",
]);
directoriesByVersion.set(279, [
  "goblint-structural-racefree-v279-20260728",
]);
directoriesByVersion.set(280, [
  "empty-compiler-barrier-linux-v280-20260728",
]);
directoriesByVersion.set(281, [
  "relational-comparator-certificate-v281-20260728",
]);
directoriesByVersion.set(282, [
  "relational-comparator-transitivity-v282-20260728",
]);
directoriesByVersion.set(283, [
  "relational-comparator-substitution-v283-20260728",
]);
directoriesByVersion.set(284, [
  "unified-native-v284-20260729",
]);
directoriesByVersion.set(285, [
  "native-residual-v285-20260729",
]);
directoriesByVersion.set(286, [
  "native-residual-v286-pointer-spin-20260729",
]);
directoriesByVersion.set(287, [
  "native-residual-v287-pointer-scope-20260729",
]);
directoriesByVersion.set(288, [
  "native-residual-v288-single-worker-20260729",
]);
directoriesByVersion.set(289, [
  "native-residual-v289-evilcollapse-20260729",
]);
directoriesByVersion.set(290, [
  "native-witness-v290-20260729",
]);
directoriesByVersion.set(291, [
  "native-guided-schedule-v291-20260730",
]);
directoriesByVersion.set(292, [
  "native-residual-v292-20260730",
]);
directoriesByVersion.set(293, [
  "native-affine-nontermination-v293-20260730",
]);
directoriesByVersion.set(294, [
  "native-modular-loop-summary-v294-20260730",
]);
directoriesByVersion.set(295, [
  "native-residual-v295-20260730",
]);
directoriesByVersion.set(296, [
  "native-residual-v296-20260730",
]);

const descriptionOverrides = {
  17: "Linear Reason Merge replaced repeated reason-vector unions. The targeted gate regressed CPU to 1.0044x, so the candidate was rejected.",
  18: "A repaired Linear Reason Merge removed the V17 defect, but the clean comparison did not establish a full-suite optimization.",
  19: "CPU hotspot audit after V17/V18; diagnostic only, with no accepted implementation or comparable full run.",
  20: "Clean adaptive residual profile used to select the next native solver mechanism; no standalone optimization claim.",
  49: "Formal design stage for interference-closed predicate reasoning. Later V50–V53 syntax, GOTO admission, and implementation gates refine this method.",
  168: "A deeper generic counterexample-unwind portfolio was tested and found too expensive; V169 moved to a semantic homogeneous-spawn witness instead.",
  194: "CIDRP added two official correct tasks, returned TRUE on task82, and slightly reduced aggregate CPU, wall, and summed task memory. N=2/N=3 replay analysis later established that the original Deagle FALSE candidates for task82 are stale pre-initialization reads, so V194 has 653 adjudicated correct results and is reclassified as successful.",
  195: "RLCC conservatively requires an identifiable region-to-lock relation before applying CIDRP. It retains the two V194 gains, restores zero wrong results, loses no V193 correct result, and is aggregate resource-neutral. The task-82 candidate witness remains semantically unvalidated.",
  196: "A broad event-availability guard repaired task 82's spurious dynamic-pointer counterexample, but exact725 lost four correct results, introduced three official wrong results, increased CPU by 7.03% and wall by 6.87%, and reduced summed memory by only 0.41%. V196 was rejected.",
  197: "Dynamic-object-only guard refinement repaired V196's static WMM errors, but exact725 still lost one V195 correct task, increased CPU by 5.21% and wall by 5.05%, and reduced summed memory by only 0.90%. V197 was rejected.",
  198: "Multi-target grouping removed only events that had no nontrivial guard. Natural formulas shrank by at most 200 clauses and one task's decisions increased from 4.18 million to 9.99 million, so V198 was rejected before exact725.",
  199: "Conditional event generation repairs the task-82 stale-read soundness defect at shared-event creation. Under manual semantic adjudication it has 652 correct and zero wrong, but versus V195 CPU rises 5.28%, wall rises 5.14%, summed memory falls only 0.75%, and Weaver buffer-alt3 is lost to timeout. It is retained as a soundness repair candidate and rejected as a performance optimization.",
  200: "Dynamic-allocation dereference guards keep the task-82 soundness repair while restoring static-object formulas to V195. Against V199 they cut CPU 3.34% and wall 3.26%, but against V195 aggregate CPU is still 1.77% higher, wall is 1.72% higher, and the task-82 gain is exchanged for a bounded_buffer timeout. V200 is retained as a soundness repair candidate and rejected as a full-suite optimization.",
  201: "Guard-conflict RF pruning soundly omits selectors for syntactically contradictory event guards. The rule fired only on constructed mutations; natural task81/83/84 pruned zero RF candidates and changed at most 60 variables and 16 clauses, with task84 decisions increasing. V201 was rejected before prior80 and exact725.",
  202: "Latest Local Write RF Dominance removes an older same-thread read-from source when a necessarily active same-address write intervenes. It passed 15/15 semantic cases and prior80 stayed 80/80 correct, but all 80 natural logs pruned zero candidates; only constructed mutations triggered it. V202 was removed and rejected before exact725.",
  203: "Property-Relevant Concurrent Event Cone removes memory-model participation for shared events outside a conservative property/synchronization/alias fixed point. One exact725 round has 653 adjudicated correct results, zero adjudicated wrong, and 72 unknown. Versus V200 it adds bounded_buffer with no lost completion while reducing aggregate CPU 3.93%, wall 3.87%, and summed memory 20.43%.",
  204: "Synchronization-Relevance Closure audited all 725 preserved V203 logs without rerunning tasks. Although 456 natural tasks reached the event cone, synchronization seeds were only 5.68% of retained events and zero timeout/OOM tasks reached this stage. The method was rejected before implementation because it cannot address the current full-suite bottleneck.",
  205: "Residual Early-Stage Attribution reused the V203 exact725 evidence and profiled the dominant 30-task timeout class once. All 30 tasks across eight families were still inside the final unbounded native symbolic-execution invocation at 60 seconds; completed wrapper stages averaged only 0.907 seconds per task. This is a bottleneck audit, not an optimization result.",
  206: "Guarded Mutex-Region Fixed Point independently reproduced the already rejected V182 Mutex-Scoped Atomic Interference method. It proved 1/6 natural gate tasks, only 48_ticket_lock in pthread-ext, and failed the frozen requirement of at least three tasks across two families. No exact725 run was performed; V206 confirms a negative boundary rather than contributing a distinct algorithm.",
  207: "Interference-Closed WP Predicate Synthesis closes the syntactic predicate basis under up to three assignment preimage rounds. It added two correct natural results, 39_rand_lock_p0 and 45_monabsex1, but both are pthread-ext; arithmetic_prog_ok timed out from cube/SAT growth. The method failed the three-task/two-family gate, so no exact725 run was performed.",
  208: "Property-Seeded WP Refinement attempted to generate assignment preimages only from assertion atoms while preserving the original control basis. A verdict-neutral eight-task audit reported one assertion seed in every analyzed thread but zero new property-seeded predicates across all 21 thread analyses. The candidate failed admission before semantic implementation; no exact725 run was performed.",
  209: "WP Origin Proof-Core Attribution was invalidated by its post-run source audit. The archived revision labeled GOTO-only actually collected assignment-RHS seeds, the variants also changed the base predicate collector, and ASSUME/GOTO logs were metric-identical. The observed 2/2 versus 0/2 table cannot support an origin claim. No natural8 or exact725 run was admitted.",
  210: "Controlled WP Seed-Origin Replication reran V209 with one immutable source and binary plus an audited runtime mode. Base counts matched across all five modes. GOTO-only correctly retained 2/2 while ASSUME-only and RHS-only retained 0/2, but it reduced generated predicates from 6,5 to only 5,5. Because one task did not shrink and evidence remained one family, no natural8 or exact725 run was admitted.",
  211: "Cyclic-GOTO WP Refinement seeded weakest-precondition closure only from GOTO instructions that lie on CFG cycles. It retained 39_rand_lock_p0 while reducing that worker from 5 to 3 generated predicates, but 45_monabsex1 has no cyclic worker GOTO and regressed from TRUE to UNKNOWN when its five acyclic-branch preimages disappeared. The semantic gate failed, so no natural8 or exact725 run was admitted.",
  212: "Property-Overlap GOTO WP Refinement selected GOTO seeds by symbol overlap with assertion expressions. At this analysis stage the properties have been lowered to paths reaching a symbol-free assert(false), so all four thread analyses reported zero assertion symbols, selected zero GOTOs, and regressed both known proofs from TRUE to UNKNOWN. No natural8 or exact725 run was admitted.",
  213: "Error-Control GOTO WP Refinement selected conditional branches whose CFG successors differ on assertion reachability. It preserved both known proofs and reduced 39_rand_lock_p0 from five to two generated worker predicates, but 45_monabsex1 remained at five because its sole GOTO controls the error path. The preregistered two-task reduction gate failed, so no natural8 or exact725 run was admitted.",
  214: "Error-Control WP Depth Minimization compared one, two, and three assignment-preimage rounds under V213's branch selector. Depth one retained 1/2; depth two was the minimum retaining 2/2 and reduced 45_monabsex1 from five to four predicates, while 39_rand stayed at two. The stage-local two-task reduction gate failed; the combined 2,4 versus V207's 6,5 was reserved for a separately preregistered successor.",
  215: "Error-Control Depth-2 Combined Natural Gate froze V213's error-path branch selector with V214's two-round closure. On natural8 it retained the same two pthread-ext proofs, converted arithmetic_prog_ok from TIMEOUT to UNKNOWN, and added no correct task or second family. Eight-row CPU, wall, and summed memory fell 51.26%, 51.17%, and 18.07% versus V207, but the coverage gate failed, so no prior or exact725 run was admitted.",
  216: "Relational Proof-Gap Audit instrumented V215 without changing verdict semantics. A five-task run retained two SAFE controls and three UNKNOWN candidates. It found constant 1 != 0 worker seeds plus missing permutation and affine lower-bound closure in tasks 31/35, and a missing join-completion-conditioned net effect in sync01. This is design evidence for a guarded affine transition domain, not a CPU, wall, memory, or verified-count improvement.",
  217: "Guarded Affine Transition Certificate adds three adjudicated-correct exact725 results from recurring mutex regions and joined one-shot workers, loses none, and has zero adjudicated wrong results. Versus V203, aggregate CPU falls 4.31% and wall falls 4.25% because three timeouts disappear, while summed memory rises 10.03% and common-correct CPU rises about 34.7% due to a duplicate Python parse/analysis pass. The algorithm is retained as a capability success; the separate-prepass launcher is not promoted.",
  218: "Integrated Guarded Affine Dispatch preserves V217's three adjudicated-correct gains and loses no V203 result while sending only 64 reached tasks through affine mode in V203's existing fixed-point subprocess. Versus V203, adjudicated correct rises 653 to 656, aggregate CPU falls 7.00%, wall falls 6.87%, and summed memory falls 0.41%; common-correct CPU is 1.0297x. Versus V217, statuses are identical while CPU falls 2.81%, wall falls 2.74%, and summed memory falls 9.48%. V218 is promoted as a full-suite optimization.",
  219: "Affine-Only Fail-Closed Dispatch was rejected by source audit before implementation. Joined one-shot proofs can return directly from affine_phase_certificate, but recurring V218 proofs require affine_template_closure followed by fixedpoint_runnert::run to establish inductiveness. Actual normalization and closure failures already return UNKNOWN early, so the proposed boundary would lose tasks 31 and 35 rather than remove redundant work. No code or benchmark run was performed.",
  220: "Delta-Cube Fixed-Point Worklist preserves all 725 statuses and the adjudicated 656/0 result, but adds no completion, increases aggregate CPU by 0.131% and wall by 0.126%, and reduces summed memory by only 0.009%. It is rejected and not promoted.",
  221: "Post-Affine Combined Proof Dispatch composes V218 affine certificates with V215 error-control depth-2 WP under a task-independent 26-task census. It adds exactly two adjudicated-correct exact725 results, loses none, reduces aggregate CPU by 5.01%, wall by 4.92%, and summed memory by 0.41%, with a 1.34% common-correct CPU geomean increase. The capability succeeds, while the two-executable prototype remains unpromoted pending single-process integration.",
  222: "Single-Process Combined Proof integrates bounded error-control WP into V218's existing fixed-point executable with an explicit BASE mode and source-shape dispatch. It matches all 725 V221 statuses at adjudicated 658/0, eliminates the second executable and duplicate parse, and slightly reduces CPU, wall, and summed memory versus V221. V222 is the accepted server-side baseline.",
  223: "Typed nondeterministic RHS support removes the cast(nondet) admission barrier on two Weaver candidates, but both remain assertion_not_proved. It adds zero completion and is rejected before prior80 or exact725.",
  224: "Native-Atomic Affine Closure exposes balanced native atomic regions to the affine collector under strict fail-closed access and balance checks. Dekker and one Weaver task have no supported region; the other has no relational property template. It adds zero completion and is rejected.",
  225: "Finite-Constant Protocol Product proves Dekker, Dekker-unfair, and Lamport in targeted gates and passes 10 semantic mutations plus prior80. Its exact725 launcher suppresses all formal .i dispatches because header declarations contain explicit-atomic names. All 725 statuses match V222 while CPU and wall rise 2.73% and 2.61%, so V225 is rejected.",
  226: "Preprocessed Atomic Dispatch preserves V225's native analyzer byte-for-byte and distinguishes actual explicit-atomic calls from header declarations. It adds exactly three TIMEOUT-to-true results with zero losses or new wrong results, while full-suite CPU, wall, and summed memory fall 5.71%, 5.70%, and 1.84%. V226 is the accepted server-side baseline.",
  227: "Weaver Residual Semantic Audit attributes 36.79% of unresolved CPU to ten Weaver timeouts and identifies a shared pre-spawn array initialization barrier in three poker tasks. Exact non-symbol transfer is unsupported; a conservative memory-havoc prototype adds zero SAFE results. V227 is rejected before regression or exact725.",
  228: "Large-Static Unwind Rescue reconstructs thirteen Goblint failures with one common suggested bound of 10001. Seven are expected-safe and six expected-unsafe. The existing rescue portfolio plus direct bounds through 32 finds zero violations; incomplete bounded success is not promoted. V228 is rejected before regression or exact725.",
  229: "libvsync Empty-Asm and Unwind Audit strictly sanitizes six unused glibc asm aliases and one hundred empty compiler barriers per task. Seven apparent successes fail the complete-unwind gate, and a reachable-error mutation is falsely SAFE under the launcher's incomplete bound. V229 is rejected before prior80 or exact725.",
  230: "Remaining UNKNOWN/ERROR Mechanism Census reconstructs 64 unresolved V226 tasks and isolates six LDV inputs rejected at Deagle's asm conversion gate. Restoring CBMC's existing asm-lowering path changes all six fast errors into 30-second timeouts and yields zero complete results; unsupported real instructions are also silently ignored. V230 is rejected before mutations, implementation, prior80, or exact725.",
  231: "Queue/Stack Large-Unwind Relation Audit corrects the apparent common bound to 401/801 and separates two queue variants requiring indexed value correspondence from two stack variants requiring a mutex-protected capacity invariant. Existing analyzers complete zero tasks, and neither single relation covers the required three natural inputs. V231 is rejected before mutations or implementation.",
  232: "Residual pthread-ext Mechanism Audit separates six V226 timeouts into pointer/CAS, non-symbol floating assignment, NetBSD mutex lifecycle, and ticket atomic reasoning. Base, affine, and error-control diagnostics complete zero tasks; the largest coherent class contains two inputs, below the preregistered three-task gate. V232 is rejected before mutations or implementation.",
  233: "Ticket-Lock Ownership Certificate proves both pthread-mutex and explicit ticket-lock encodings under one structural ownership theorem. It passes 11 semantic mutations and prior80, and exact725 gains both ticket tasks with no new wrong verdict. However, global ownership-mode integration loses pthread-ext/39_rand_lock_p0_vs from true to TIMEOUT. V233 is rejected despite adjudicated correct increasing from 661 to 662 and aggregate CPU, wall, and summed memory falling 3.39%, 3.32%, and 1.18%.",
  234: "Structurally Dispatched Ticket Ownership selects 9/725 inputs for a fail-closed five-second ownership prepass and falls back to unchanged V226 behavior on UNKNOWN. Exact725 changes exactly the two ticket tasks from TIMEOUT to true with zero losses and zero new wrong. Adjudicated correct rises from 661 to 663, aggregate CPU and wall fall 5.95% and 5.83%, and summed memory rises 0.67%. V234 is accepted as the isolated server-side baseline.",
  235: "Constant-Property Discharge was rejected before implementation. Both motivating sysmon tasks contain a constant-false assertion inside reach_error; safety depends on call-site reachability, not on every property simplifying to true.",
  236: "Mutex-State Call Reachability was rejected before integration. Constant guards leave genuine mutex-model error edges, goto-instrument constant propagation warns that it is unsound, and standalone interval analysis omits the pthread worker.",
  237: "Lock-Allocated Index-Region Ownership selects exactly 2/725 inputs and proves both SSSC12 variants with a GOTO-level non-wrap, disjoint-interval, footprint, and property certificate. Twelve mutations are rejected, prior80 remains 80/80, and exact725 has exactly two TIMEOUT-to-true gains with zero losses and zero new wrong. Adjudicated correct rises 663 to 665; CPU and wall fall 5.86% and 5.82%, while summed memory rises 1.31%.",
  238: "Post-Store Stable-Cell Certificate selects exactly 2/725 inputs and proves both NVRAM post-store equality tasks with resolved lifecycle, call graph, unique allocation origin, non-aliasing, and other-worker exclusion. Twelve mutations are rejected, prior80 remains 80/80, and exact725 changes only the two selected tasks from TIMEOUT to true with zero losses and zero new wrong. Adjudicated correct rises 665 to 667; CPU, wall, and summed memory fall 6.52%, 6.44%, and 1.31%.",
  239: "Serialized Stack-Capacity Invariant selects exactly 3/725 inputs and proves the two unresolved bounded-stack tasks from the invariant 0 <= top <= pushes_completed <= capacity. The GOTO proof dynamically derives the counter, array capacity, worker roles, mutex, unit updates, error-control branches, and exact counter footprints without task names or version-number annotations. Nineteen semantic mutations are rejected, prior80 remains 80/80, and exact725 changes only stack_longer-2 and stack_longest-2 from ERROR to true with zero losses and zero new wrong. Adjudicated correct rises 667 to 669; CPU, wall, and summed memory fall 0.62%, 0.59%, and 1.04%.",
  240: "Serialized Queue Sequence Correspondence selects exactly 3/725 inputs and proves the two unresolved bounded-queue tasks by relating producer writes, FIFO queue contents, and the reference sequence under whole-worker mutex serialization. The GOTO proof derives objects, capacity, lifecycle, phase flags, operation bodies, index updates, property shape, and exact footprints without task names, paths, fixed capacities, expected labels, or version-number annotations. Twenty-three semantic mutations are rejected, prior80 remains 80/80, and exact725 changes only queue_ok_longer and queue_ok_longest from ERROR to true with zero losses and zero new wrong. Adjudicated correct rises 669 to 671; CPU, wall, and summed memory fall 0.48%, 0.44%, and 3.92%.",
  241: "Atomic Idempotent-Loop Commuting Sequentialization selected exactly 3/725 Weaver poker tasks and passed 18 rejecting mutations plus prior80 80/80. The first full runs showed apparent gains but also two non-candidate timeouts because the extended transform leaked into the ordinary fallback path. After candidate-only gating and faithful abort-as-nonreturning normalization, all remaining unwind assertions passed but the reachability property failed. V241 is rejected; V240 metrics and adjudicated 671 remain the accepted baseline.",
  242: "Large Static Complete-Unwind Admission Audit tested all 13 unresolved Goblint regression inputs at unwind 10001 with explicit unwinding assertions. Five expected-safe tasks appeared provable, but three expected-unsafe tasks (71, 72, and 86) were also reported safe and four tasks timed out. Loop completeness did not establish concurrency completeness, so V242 was rejected before implementation and V240 metrics remain the baseline.",
  243: "Nonnegative Oscillator Monitor derives an atomic position, atomic loop flag, private toggles, symmetric positive weights, initialization, monitor, complete create/join lifecycle, overflow bound, and sole post-join error from source structure. It selects exactly 1/725 input and rejects 16/16 semantic mutations. Prior80 remains 80/80; exact725 changes only parallel-misc-4 from TIMEOUT to true with zero losses and zero new wrong. Official correct rises 670 to 671 and adjudicated correct rises 671 to 672; CPU and wall fall 3.11% and 3.05%, while summed memory rises 0.15%.",
  244: "Monotone Potential Overflow Audit tested whether V243's nonnegative-potential theorem could extend to parallel-misc-5. The source has unbounded signed increments and no arithmetic upper bound. A signed-char width-reduced mutation reaches the property at unwind 140 after wraparound, so the mathematical-integer invariant is not sound for Deagle bit-vectors. V244 was rejected before implementation and V243 remains the baseline.",
  245: "Dynamic TLS Calloc-Zero Certificate reads the actual preprocessed input and derives the TLS pointer/type, calloc length, zero assertion loop, later write loop, dynamic thread count, worker, handle array, and matched create/join bounds. It selects exactly 1/725 input and rejects 16/16 semantic mutations. Prior80 remains 80/80; exact725 changes only thread-local-value-dynamic from TIMEOUT to true with zero losses and zero new wrong. Official correct rises 671 to 672 and adjudicated correct rises 672 to 673; CPU and wall fall 3.46% and 3.40%, while summed memory rises 1.62%.",
  246: "TLS Destructor Counterexample Certificate reads the actual preprocessed input and derives the pthread key, registered destructor, worker, thread handle, stored non-null value, matching destructor rejection, and join lifecycle. It selects exactly 1/725 input and rejects 16/16 counterexample-breaking mutations. Prior80 remains 80/80; exact725 changes only tls_destructor_worker from unknown to correct false(unreach-call), with zero losses and zero new wrong. Official correct rises 672 to 673 and adjudicated correct rises 673 to 674; CPU, wall, and summed memory change only +0.008%, +0.012%, and +0.24%.",
  247: "Partitioned Count Reduction derives the array length, positive thread count, divisible partition width, disjoint worker intervals, identical equality predicate, mutex-protected local-to-global reduction, complete create/join lifecycle, and full sequential recount. It selects exactly 1/725 input and rejects 16/16 semantic mutations. Prior80 remains 80/80; exact725 changes only pthread-finding-k-matches from ERROR to true with zero losses and zero new wrong. Official correct rises 673 to 674 and adjudicated correct rises 674 to 675; CPU, wall, and summed memory change by +0.264%, +0.249%, and +1.250%.",
  248: "Finite Two-Sided Floating Disjunction derives a positive interval count bounded by eight, one finite positive term per worker, common mutex reduction, complete lifecycle, a finite area bound of 32, and a positive-width two-sided property. It selects exactly 1/725 input and rejects 17/17 semantic mutations, including NaN and zero-divisor cases. Prior80 remains 80/80; exact725 changes only pthread-numerical-integration from TIMEOUT to true with zero losses and zero new wrong. Official correct rises 674 to 675 and adjudicated correct rises 675 to 676; CPU, wall, and summed memory fall by 3.467%, 3.422%, and 0.232%.",
  249: "Completion-Flag Arithmetic Series proves partial correctness without assuming condition-variable fairness. It derives the unique accumulator and flag writer, private loop sequence 0 through N-1, final +N, completion-flag ordering, matching create/join lifecycle, and triangular-number property. It selects exactly 1/725 input and rejects 17/17 semantic mutations. Prior80 remains 80/80; exact725 changes only arithmetic_prog_ok from TIMEOUT to true with zero losses and zero new wrong. Official correct rises 675 to 676 and adjudicated correct rises 676 to 677; CPU, wall, and summed memory fall by 3.407%, 3.357%, and 0.136%.",
  250: "Nonzero CAS Seed Invariant derives rejection sampling that excludes zero and the prior seed, exact successful and failed CAS semantics, state-lock initialization ordering, monitor admission, unique seed writers, and a positive-modulus range property. It selects exactly 1/725 input and rejects 18/18 semantic mutations. Prior80 remains 80/80; exact725 changes only 08_rand_cas from TIMEOUT to true with zero losses and zero new wrong. Official correct rises 676 to 677 and adjudicated correct rises 677 to 678; CPU, wall, and summed memory fall by 3.733%, 3.635%, and 0.204%.",
  251: "Monotone Chunk Maximum derives a six-element array, two-element aligned chunks, complete offset bounds, local update-before-check, one common mutex, and a global maximum that can only increase. It selects exactly 1/725 input and rejects 18/18 semantic mutations. Prior80 remains 80/80; exact725 changes only 11_fmaxsymopt from TIMEOUT to true with zero losses and zero new wrong. Official correct rises 677 to 678 and adjudicated correct rises 678 to 679; CPU and wall fall 4.011% and 3.732%, while summed memory rises 0.201%.",
  252: "Linear/Tiled Copy Equivalence derives nonnegative row and column bounds, a checked row-major product, distinct linear/source/tiled arrays, complete one-dimensional and nested two-dimensional copy loops, matched create/join lifecycle, and the negated indexed equality property. It selects exactly 1/725 input and rejects 18/18 semantic mutations. Prior80 remains 80/80; exact725 changes only loop-tiling-eq from TIMEOUT to true with zero losses and zero new wrong. Official correct rises 678 to 679 and adjudicated correct rises 679 to 680; CPU, wall, and summed memory fall 4.169%, 4.265%, and 1.470%.",
  253: "Atomic Queue Occupancy Value derives a dynamic FIFO, distinguished value, front, occupancy, capacity, nondeterministic factory, balanced atomic producer/consumer regions, checked indices, absence of post-factory queue writes, complete lifecycle, and the negated target property. It selects exactly 1/725 input and rejects 18/18 semantic mutations. Prior80 remains 80/80; exact725 changes only test-context1 from TIMEOUT to true with zero losses and zero new wrong. Official correct rises 679 to 680 and adjudicated correct rises 680 to 681; CPU, wall, and summed memory fall 4.449%, 4.357%, and 0.337%.",
  254: "Isomorphic Modular Fold Pair derives exactly two identical unsigned folds, their common iteration count and addend, two atomic consecutive-slot admissions, one observer, valid adjacent indices, stable queue contents, complete lifecycle, and the negated equality property. It selects exactly 1/725 input and rejects 18/18 semantic mutations. Prior80 remains 80/80; exact725 changes only popl20-more-multiply-verify from TIMEOUT to true with zero losses and zero new wrong. Official correct rises 680 to 681 and adjudicated correct rises 681 to 682; CPU, wall, and summed memory fall 4.850%, 4.735%, and 2.062%.",
  255: "Conserved-Sum Nontermination Barrier rechecked parallel-misc-5 using the invariant position = left + right with nonnegative components. Its task-independent selector admits 1/725, rejects 18/18 semantic mutations, emits a successful direct smoke certificate, and preserves prior80 80/80. The method is rejected before exact725 because the unbounded loops use signed machine integers: overflow is undefined in ISO C and can make the monitored position negative under wrapping semantics. V244 had already rejected the same mechanism with a width-reduced wraparound mutation, so V255 is a duplicate-candidate regression audit and V254 remains the accepted baseline.",
  256: "Native consolidated redo for V256–V257. A production GOTO-model main/worker-prefix transform derives the worker from a canonical create loop and searches finite worker depths 7 and 11; it contains no task name, path, expected verdict, target index, or fixed source grammar. The changed native binary (SHA-256 67963e93…6165) directly produces counterexamples for race_reach_71, race_reach_72, and race_reach_77. Prior80 is 80/80. Exact725 changes only those three ERROR results to correct false(unreach-call), with zero losses and zero new wrong. Adjudicated coverage rises 682 to 685; CPU and wall fall 2.400% and 2.685%, while summed memory rises 4.381%. This single exact measurement is not counted twice.",
  257: "V257 is recovered by the same consolidated native V256–V257 binary and exact725 run as V256. The generic main/worker-prefix transform also finds race_reach_77 without a V257-specific rule. This row marks the second historical goal as natively recovered but keeps the same 685 coverage, CPU, wall, and memory endpoint, so the shared gain is not added twice. Historical wrapper evidence remains separately retained.",
  258: "Native V258 redo. A production GOTO under-approximation derives two distinct worker classes, one nested initialization prefix, the propagated worker index, and one feasible assertion/update branch pairing. It contains no task name, path, expected verdict, source variable name, or version marker. The changed native binary (SHA-256 d22e62d9…ccd21) directly finds race_reach_90. Admission mutations are 19/19, natural siblings admit only the target structure, and prior80 is 80/80. Exact725 changes only race_reach_90 from ERROR to correct false(unreach-call), with zero losses and zero new wrong. Official correct rises 684 to 685 and adjudicated correct rises 685 to 686. CPU and wall rise 4.478% and 4.687%, while summed memory falls 0.807%; V258 is a coverage gain, not a speedup.",
  259: "Native V259 redo. A production GOTO under-approximation derives nested initialization, two bounded lookup domains, a cross-domain same-field assignment, one homogeneous worker class, propagated worker indices, matched locks, balanced updates, and the assertion branch. It contains no task name, path, expected verdict, or version marker, and rejected candidates cannot leave partial GOTO edits. T93 and C01–C18 are rejected; among 56 natural inputs only the target-equivalent N054 is admitted. Prior80 is 80/80. Exact725 changes only race_reach_92 from ERROR to correct false(unreach-call), with zero losses and zero new wrong. Official correct rises 685 to 686 and adjudicated correct rises 686 to 687; CPU and wall fall 4.194% and 4.732%, while summed memory rises 3.503%.",
  260: "Native V260 redo. A production GOTO under-approximation derives initialized object and mutex arrays, two independent bounded worker choices, a pointer-returning indexed lookup, matched indexed lock ownership, balanced updates, and the assertion branch. It contains no task name, path, expected verdict, source variable name, or version marker. The paired control and M01–M18 are rejected; the natural scan admits only the target structure under the applicable assertion property. Prior82 is 82/82. Exact725 changes only race_reach_86 from ERROR to correct false(unreach-call), with zero losses and zero new wrong. Official correct rises 686 to 687 and adjudicated correct rises 687 to 688; CPU, wall, and summed memory rise 0.265%, 0.339%, and 1.540%.",
  261: "Native V261 redo. A sound production GOTO reduction derives one zero-initialized shared scalar, exact common-mutex helper calls, a balanced plus-one/minus-one worker effect, a zero assertion protected by the same mutex, complete spawn/join lifecycle, and a four-mention whole-model census. It contains no task name, path, expected verdict, source variable name, or version marker. All 18 premise mutations are rejected and the natural scan admits only the target structure. Prior83 is 83/83. Exact725 changes only race_reach_05 from ERROR to correct true, with zero losses and zero new wrong. Official correct rises 687 to 688 and adjudicated correct rises 688 to 689; CPU and wall rise 0.264% and 0.233%, while summed memory falls 1.154%.",
  262: "Native V262 redo. A sound production GOTO reduction derives one zero-initialized shared scalar, a common worker mutex, a balanced plus-one/minus-one worker effect, and one nondeterministic guard whose identical GOTO condition dominates main's direct lock, zero assertion, and matching unlock. It contains no task name, path, expected verdict, source variable name, or version marker. Two paired controls and all 18 premise mutations are rejected; the natural scan admits only the target structure. Prior84 is 84/84. The first exact candidate exposed an unbound-iterator rejection-path defect and was rejected with seven losses; the repaired candidate restores all seven and changes only race_reach_08 from ERROR to correct true. Official correct rises 688 to 689 and adjudicated correct rises 689 to 690; CPU, wall, and summed memory rise 0.608%, 0.591%, and 0.605%.",
  263: "Native V263 redo. A sound production GOTO reduction derives one zero-initialized Boolean predicate, a monotone writer under a common mutex, the matching condition-variable broadcast, a rechecking wait loop, the post-loop property guard, complete predicate-write and error-site censuses, and the canonical worker-create loop. It contains no task name, path, expected verdict, source variable name, or version marker. The explicit sibling and all 18 premise mutations are rejected; the three-input natural scan admits only the target structure. Prior85 is 85/85 and all seven V262 loss sentinels retain their correct outcomes. Exact725 changes only the NetBSD sysmon pthread task from TIMEOUT to correct true, with zero losses and zero new wrong. Official correct rises 689 to 690 and adjudicated correct rises 690 to 691; CPU, wall, and summed memory rise 5.135%, 6.575%, and 2.804%.",
  264: "Explicit Boolean-Lock Protocol Safety was rejected at design review. The draft derived identifiers but still required nine fixed service roles and exact body grammars, which is task specialization rather than a general verifier optimization. No source, binary, prior set, or exact725 run changed.",
  265: "Unwind Progress Logging Demotion was rejected at the natural performance gate. A corrected 36-run comparison reduced output volume but produced mixed, noise-sized CPU and wall changes across three tasks. No prior86 or exact725 run was authorized, and the V263 source and binary were restored.",
  266: "Native Mutex-Zero Fixed-Point Safety derives a unique zero-initialized scalar, one invariant mutex, net-zero main and worker transitions, two real zero properties, and an off-mutex worker transition reachable only after observing nonzero under the invariant mutex. The resulting zero state is inductive. The implementation contains no task name, path, expected verdict, identifier, or fixed source grammar. Eighteen mutations are rejected, only T60 is admitted among 56 natural siblings, and prior86 is 86/86. Exact725 changes only T60 from ERROR to correct true, with zero losses and zero new wrong results. Official/adjudicated correct rise to 691/692; CPU, wall, and summed memory rise 0.498%, 0.441%, and 0.849%.",
  267: "Native Resolved-Worker Zero-Sum Safety derives a dormant worker class, complete create/join lifecycle, a uniquely resolved static function pointer, one reachable helper with a balanced +1/-1 transition under an invariant mutex, and a zero assertion protected by the same mutex. It contains no task name, path, expected verdict, source identifier, or version marker. All 18 valid premise mutations are rejected, only T28 is admitted among 56 natural siblings, and prior87 remains 87/87. Exact725 changes T28 from ERROR to correct true with zero losses and zero new wrong results. A separate parallel-misc-5.wvr timeout also completes correctly but is conservatively treated as run variance, not a V267 coverage claim. Official/adjudicated correct are 693/694; CPU, wall, and summed memory change -9.557%, -9.311%, and -0.528% versus V266.",
  268: "Native Aggregate-Member Lock-Alias Safety derives a complete two-base alias partition over same-typed static aggregates. The worker protects one scalar member with its sibling mutex; main derives both its scalar and mutex pointers from the same branch-selected aggregate, so same-base accesses serialize and different-base accesses are disjoint. It contains no task name, path, expected verdict, source identifier, or version marker. Two explicit controls and all 18 valid premise mutations reject; among 56 natural siblings only T79 is admitted; prior88 is 88/88. Exact725 changes only T79 from ERROR to correct true, with zero losses and zero new wrong results. Official/adjudicated correct are 694/695; CPU, wall, and summed memory change -8.930%, -9.535%, and +0.115% versus V267.",
  269: "Indexed-List Race Safety was rejected at the truth gate. T91 and T93 both initialize a slot-1 node with datum 1, and a worker can immediately choose the original zero-assertion branch. Mechanically bounded, fully unwound sequential witnesses fail the original reach_error assertion for both tasks. No native candidate, wrapper gain, prior run, performance run, or exact725 run was authorized; V268 remains the accepted baseline.",
  270: "Native Nested-Lifecycle Last-Writer Safety derives two nested create/join lifecycles, correlated create return values, all-path joins, private finite-state protocol control, mutex-dominated child properties, outer ordering, immediate store/assert pairs, and complete write/address-escape censuses. It contains no task name, path, expected verdict, source identifier, asserted literal, or version marker. All 18 mutations reject; only the target is admitted among 14 natural neighbors; prior89 is 89/89. Exact725 changes only race-4_1-thread_local_vars from TIMEOUT to correct true, with zero losses and zero new wrong results. Official/adjudicated correct are 695/696; CPU and wall rise 3.261% and 4.262%, while summed memory falls 0.825%.",
  271: "Native Boolean Atomic-Lock Region Safety proves the property with a fail-closed interprocedural finite-state analysis. Prior90 is 90/90. Exact725 has zero old-correct losses and zero new wrong results, and changes one task from timeout to correct true. Official/adjudicated correct reach 696/697; CPU, wall, and memory all improve versus V270.",
  272: "Rejected at the truth gate. A 32-bit wraparound counterexample disproves the proposed chunked-iterator equivalence for non-power-of-two chunk widths. No production source or wrapper changed.",
  273: "Rejected at the target performance gate. Native commuting sequentialization recognizes the two poker-hand candidates, but both remain above the 65-second limit. No production source changed.",
  274: "Rejected at the natural correctness gate. Empty compiler-barrier parsing alone produced incorrect failed verdicts on the libvsync family, so the candidate was restored and no coverage was claimed.",
  275: "Rejected at the target correctness gate. A complete bounded Deagle run reaches the work-steal queue error assertion despite the expected-true label; no code was accepted.",
  276: "Rejected at native design feasibility. A concrete 42-step SC schedule reaches the SafeStack ABA property, but the demonstrated schedule depends on task-specific roles and values. No production source changed.",
  277: "Rejected at the target performance gate. The smallest sound explicit-create reduction still retains 3,868 retained events and times out. No production source changed.",
  278: "Rejected at the natural correctness gate. Correct pthread create/join bodies show two correct libvsync gains but also one new wrong result, so the accepted source was restored byte-for-byte.",
  279: "Rejected at the truth gate. Both expected-true Goblint tasks have a direct single-thread violation at the first element, whose value is 29; the executable uses one worker and exits 10. Accepting them would therefore introduce a wrong result.",
  280: "Rejected at the Linux applicability gate. Five invalid asm controls rejected, but all residuals contain nonempty x86 hardware instructions. The candidate adds zero coverage.",
  281: "Native comparator antisymmetry adds one correct Weaver task with zero old-correct losses and zero new wrong results. The clean prior90 is 90/90. One stale-object contaminated run is retained but excluded.",
  282: "Native comparator transitivity adds one correct Weaver task. Exact725 reaches 698 official / 699 adjudicated correct with zero old-correct losses and zero new wrong results; prior90 remains 90/90.",
  283: "Native comparator substitution preserves 698 official / 699 adjudicated correct with zero old-correct losses and zero new wrong results. Prior90 remains 90/90 and the native correctness witness passes WitnessLint. The displayed 335.43 minutes is the artifact-backed research-to-acceptance span: the server-side target and release gates are concentrated in 05:13:58–05:27:27, with an approximately 5 hour 20 minute gap after the initial local plan artifact. The final exact725 batch itself took about 99.6 seconds.",
  284: "Unified native V284 uses one deagle_exe and removes all three Python verdict-certificate modules. The wrapper performs bounded structural routing and argument selection only; Deagle performs admission, proof, verdict, and witness generation. Exact725 reaches 699 official / 700 adjudicated correct, adding only arraylock with zero old-correct losses and zero new wrong results. Final prior90 is 90/90 and the 3,227-byte witness passes WitnessLint. The displayed 539.56 minutes is a research-and-acceptance wall-clock span covering 156 experiment directories, solver-cliff root-cause work, native restoration of 33 certificate-dependent tasks, and all release gates; the final exact725 batch itself took 84.08 seconds and final prior90 took 9.52 seconds.",
  285: "Native V285 extends Deagle's pure-spin analysis with caller-path reservation dominance and a fail-closed inlined proof that every retrying iteration is shared-state stuttering. One deagle_exe performs admission, proof, verdict, and witness generation; the wrapper remains limited to bounded routing and argument selection. Exact725 reaches 700 official / 701 adjudicated correct, changing only libvsync/ticketlock from unknown to correct true with zero V284-correct losses and zero new wrong results. Prior90 remains 90/90, ticketlock and arraylock witnesses pass WitnessLint, and aggregate CPU, wall, and summed memory change -0.400%, -0.907%, and +0.947% against the contemporaneous V284 control. The displayed 183.42 minutes is the strictly post-V284 development-to-accepted-commit span; the earlier 08:55 relational-fold run is discarded.",
  286: "Native V286 tested a single-loop pointer-spin collapse in one deagle_exe with an unchanged wrapper. Prior90 remained 90/90 and cnalock changed from unknown to correct true, but accepted-V285 ticketlock regressed from correct true to unknown. Exact725 therefore remains 700 official / 701 adjudicated correct, with one old-correct loss and zero net coverage gain. CPU, summed wall, and summed memory change +1.147%, +1.008%, and +0.084% against V285. V286 fails the no-regression release gate; its source is not committed or pushed.",
  287: "Native V287 scopes the reservation-free pointer exception to exactly one marked spin loop while preserving V285's reservation and stuttering-retry proofs. One deagle_exe performs admission, proof, verdict, and witness generation; the byte-identical wrapper performs bounded routing and argument selection only. Exact725 reaches 701 official / 702 adjudicated correct, changing only libvsync/cnalock from unknown to correct true with zero V285-correct losses and zero new wrong results. Prior90 remains 90/90 and the 3,223-byte witness passes WitnessLint. CPU, summed wall, and summed memory change +0.601%, +0.532%, and -0.077% against V285.",
  288: "Native V288 derives two nested initialization domains and one homogeneous worker class from the GOTO model, retains domains 0 and 1, fully initializes the retained inner domain, and materializes one representative worker fixed to domain 1. One deagle_exe performs admission, counterexample search, verdict, and witness generation; the byte-identical wrapper performs bounded routing and argument selection only. Exact725 changes only expected-true 28-race_reach_91-arrayloop2_racefree from ERROR to false(unreach-call): official correct remains 701, while semantic adjudication rises from 702 to 703 because the source initializes a retained slot-1 node with nonzero datum and the worker's zero assertion is reachable. There are zero V287-correct losses and no other new wrong results; task93 remains unknown. Prior90 is 90/90, six premise-breaking mutations reject, and the 219,691-byte violation witness passes WitnessLint as a format gate. CPU, summed wall, and summed memory change -0.171%, -0.228%, and +0.351% against V287.",
  289: "Native V289 relaxed one structural admission boundary and changed only task93 from ERROR to false(unreach-call), while Prior90 remained 90/90. The emitted GraphML still used the shortened outer-initialization projection and was not an execution of the original program, so the candidate failed the semantic witness gate. Its four-line source change was not committed or pushed. The displayed interval ends at the contemporaneous V288 control completion; later documentation mtimes are excluded so V290 begins strictly afterward.",
  290: "Unified native V290 treats the reduced execution only as a guide, then processes and solves the untransformed original GOTO model inside the same deagle_exe. Verdict and GraphML come only from that second solve; replay fails closed on missing choices or property mismatch. Exact725 remains 701 official and rises from 703 to 704 adjudicated correct by changing only task93 from ERROR to false(unreach-call), with zero V288-correct losses and zero new genuine wrong results. Prior90 is 90/90. Aggregate CPU, wall, and summed memory change +3.35%, +3.31%, and +3.03% against V288. The wrapper is unchanged and production code contains no benchmark identifier, expected label, or target source-line condition.",
  291: "Native V291 retains function-prefix equality facts during pure-spin retry admission and prunes prefix CFG branches that cannot reach the marked loop. One unified deagle_exe performs admission, proof, verdict, and correctness-witness generation; the wrapper is unchanged. Under a contemporaneous N8 paired Exact725 comparison, the only status change is libvsync/rec_ticketlock from unknown to true(correct), with zero V290-correct losses and zero new wrong results. Prior90 is 90/90 and the 3,457-byte witness passes WitnessLint. Against the paired V290 control, CPU changes +0.867%, summed wall +0.807%, and summed memory -1.122%. Because the restarted server exposes 8 physical cores rather than the historical 48-worker environment, V291 raw resource totals are displayed but deliberately disconnected from historical resource trend comparisons.",
  292: "V292 tested two native residual directions and rejected both before release testing. Generalizing the exactly-one pure-read admission allowed four more libvsync tasks into Deagle, but all still exceeded 45 seconds. A bounded-progress feasibility study on SafeStack likewise exceeded 90 seconds after supplying bound 3 and 9-11 object bits. The six LDV front-end residuals contain real x86 instructions and were not lowered as empty barriers. Coverage gain is zero; production C++ and the wrapper remain unchanged, so Prior90 and Exact725 were not run.",
  293: "V293 rejected two native directions before release testing. An affine nontermination proof was unsound under signed bit-vector wraparound and was not implemented. A generic high-fan-in read-from selector built in one deagle_exe, but the corrected elimination-backoff target still exhausted 4 GB and changed CPU, wall, and peak RSS by +3.46%, +3.50%, and +0.64% against the identical V291 baseline. Coverage gain is zero; production C++ and the wrapper remain unchanged, so Prior90 and Exact725 were not run.",
  294: "Native V294 applies an exact modular closed form to fail-closed unsigned accumulation loops only after native commuting sequentialization has removed the concurrent lifecycle. One unified deagle_exe owns admission, transformation, proof, verdict, and witness generation; the wrapper is byte-identical to V291. Under a contemporaneous N8 paired Exact725 comparison, only mult-comm, mult-dist, and mult-flipped-dist change from timeout to correct true, reaching 696 official / 708 adjudicated correct with zero old-correct losses and zero new wrong results. Prior90 remains 90/90, all three GraphML witnesses pass WitnessLint's format check, and paired CPU, wall, and summed memory change -13.216%, -12.726%, and -3.138%.",
  295: "Native V295 generalizes the exact event-free local unit-increment acceleration from zero initialization to arbitrary local initial values using the closed form x < bound ? bound : x. One unified deagle_exe owns admission, transformation, backend proof, verdict, and witness generation; the wrapper is byte-identical to V294. Under a contemporaneous N8 paired Exact725 comparison, only test-easy11 changes from timeout to correct true, reaching 697 official / 709 adjudicated correct with zero old-correct losses and zero new wrong results. Prior90 remains 90/90, the 3,452-byte correctness witness passes WitnessLint's format check, and paired CPU, wall, and summed memory change -4.955%, -4.818%, and -1.656%.",
  296: "Native V296 derives fully joined workers whose private Boolean phase alternates equal opposite updates to one atomic scalar for an even unsigned step count. It replaces the proven identity transition word and leaves verdict and witness generation to the ordinary backend in one deagle_exe; the wrapper is byte-identical to V295. Under a contemporaneous N8 paired Exact725 comparison, only parallel-misc-2 changes from timeout to correct true, reaching 698 official / 710 adjudicated correct with zero old-correct losses and zero new wrong results. Prior90 remains 90/90, the 3,460-byte correctness witness passes WitnessLint's format check, and paired CPU, wall, and summed memory change -4.669%, -4.412%, and -0.746%.",
};

const timingOverrides = {
  296: {
    version: 296,
    directory: "native-residual-v296-20260730",
    available: true,
    start_epoch_s: 1785360356,
    end_epoch_s: 1785361272,
    start_iso: "2026-07-29T21:19:36.000Z",
    end_iso: "2026-07-29T21:34:52.000Z",
    duration_minutes: 15.266666666666667,
    evidence_kind: "candidate_plan_birth_to_release_witness_gate",
  },
  295: {
    version: 295,
    directory: "native-residual-v295-20260730",
    available: true,
    start_epoch_s: 1785358627,
    end_epoch_s: 1785360026,
    start_iso: "2026-07-29T20:57:07.000Z",
    end_iso: "2026-07-29T21:14:06.000Z",
    duration_minutes: 16.983333333333334,
    evidence_kind: "candidate_plan_birth_to_release_witness_gate",
  },
  294: {
    version: 294,
    directory: "native-modular-loop-summary-v294-20260730",
    available: true,
    start_epoch_s: 1785356309,
    end_epoch_s: 1785358247,
    start_iso: "2026-07-29T20:18:29.000Z",
    end_iso: "2026-07-29T20:50:47.000Z",
    duration_minutes: 32.3,
    evidence_kind: "candidate_source_birth_to_release_gate_completion",
  },
  293: {
    version: 293,
    directory: "native-affine-nontermination-v293-20260730",
    available: true,
    start_epoch_s: 1785355161,
    end_epoch_s: 1785355812,
    start_iso: "2026-07-29T19:59:21.000Z",
    end_iso: "2026-07-29T20:10:12.000Z",
    duration_minutes: 10.85,
    evidence_kind: "candidate_plan_birth_to_paired_feasibility_rejection",
  },
  292: {
    version: 292,
    directory: "native-residual-v292-20260730",
    available: true,
    start_epoch_s: 1785354190,
    end_epoch_s: 1785354913,
    start_iso: "2026-07-29T19:43:10.000Z",
    end_iso: "2026-07-29T19:55:13.000Z",
    duration_minutes: 12.05,
    evidence_kind: "candidate_directory_birth_to_feasibility_rejection",
  },
  291: {
    version: 291,
    directory: "native-guided-schedule-v291-20260730",
    available: true,
    start_epoch_s: 1785349999,
    end_epoch_s: 1785353611,
    start_iso: "2026-07-29T18:33:19.000Z",
    end_iso: "2026-07-29T19:33:31.000Z",
    duration_minutes: 60.2,
    evidence_kind: "candidate_worktree_birth_to_accepted_remote_commit",
  },
  290: {
    version: 290,
    directory: "native-witness-v290-20260729",
    available: true,
    start_epoch_s: 1785336492,
    end_epoch_s: 1785349328,
    start_iso: "2026-07-29T14:48:12.000Z",
    end_iso: "2026-07-29T18:22:08.000Z",
    duration_minutes: 213.93333333333334,
    evidence_kind: "candidate_worktree_birth_to_accepted_remote_commit",
  },
  289: {
    version: 289,
    directory: "native-residual-v289-evilcollapse-20260729",
    available: true,
    start_epoch_s: 1785333392,
    end_epoch_s: 1785335874.431224,
    start_iso: "2026-07-29T13:56:32.000Z",
    end_iso: "2026-07-29T14:37:54.431Z",
    duration_minutes: 41.37385373333333,
    evidence_kind: "candidate_worktree_birth_to_contemporaneous_control_completion",
  },
  288: {
    version: 288,
    directory: "native-residual-v288-single-worker-20260729",
    available: true,
    start_epoch_s: 1785331545,
    end_epoch_s: 1785332709,
    start_iso: "2026-07-29T13:25:45.000Z",
    end_iso: "2026-07-29T13:45:09.000Z",
    duration_minutes: 19.4,
    evidence_kind: "candidate_worktree_birth_to_remote_source_confirmation",
  },
  287: {
    version: 287,
    directory: "native-residual-v287-pointer-scope-20260729",
    available: true,
    start_epoch_s: 1785329142,
    end_epoch_s: 1785330684,
    start_iso: "2026-07-29T12:45:42.000Z",
    end_iso: "2026-07-29T13:11:24.000Z",
    duration_minutes: 25.7,
    evidence_kind: "candidate_worktree_birth_to_release_gate_completion",
  },
  286: {
    version: 286,
    directory: "native-residual-v286-pointer-spin-20260729",
    available: true,
    start_epoch_s: 1785327577,
    end_epoch_s: 1785328584.359225,
    start_iso: "2026-07-29T12:19:37.000Z",
    end_iso: "2026-07-29T12:36:24.359Z",
    duration_minutes: 16.789320416666667,
    evidence_kind: "candidate_worktree_birth_to_exact725_end",
  },
  285: {
    version: 285,
    directory: "native-residual-v285-20260729",
    available: true,
    start_epoch_s: 1785307448,
    end_epoch_s: 1785318453,
    start_iso: "2026-07-29T06:44:08.000Z",
    end_iso: "2026-07-29T09:47:33.000Z",
    duration_minutes: 183.41666666666666,
    evidence_kind: "v285_development_to_accepted_native_commit_window",
  },
  284: {
    version: 284,
    directory: "unified-native-v284-20260729",
    available: true,
    start_epoch_s: 1785274505.525093,
    end_epoch_s: 1785306879.1262665,
    start_iso: "2026-07-28T21:35:05.525Z",
    end_iso: "2026-07-29T06:34:39.126Z",
    duration_minutes: 539.5600195566813,
    evidence_kind: "full_v284_development_and_unified_redo_artifact_window",
  },
  283: {
    version: 283,
    directory: "relational-comparator-substitution-v283-20260728",
    available: true,
    start_epoch_s: 1785254002,
    end_epoch_s: 1785274128,
    start_iso: "2026-07-28T15:53:22.000Z",
    end_iso: "2026-07-28T21:28:48.000Z",
    duration_minutes: 335.43333333333334,
    evidence_kind: "local_artifact_window",
  },
  282: {
    version: 282,
    directory: "relational-comparator-transitivity-v282-20260728",
    available: true,
    start_epoch_s: 1785248802,
    end_epoch_s: 1785253108,
    start_iso: "2026-07-28T14:26:42.000Z",
    end_iso: "2026-07-28T15:38:28.000Z",
    duration_minutes: 71.76666666666667,
    evidence_kind: "local_and_server_artifact_window",
  },
  281: {
    version: 281,
    directory: "relational-comparator-certificate-v281-20260728",
    available: true,
    start_epoch_s: 1785242814,
    end_epoch_s: 1785248383,
    start_iso: "2026-07-28T12:46:54.000Z",
    end_iso: "2026-07-28T14:19:43.000Z",
    duration_minutes: 92.81666666666666,
    evidence_kind: "local_and_server_artifact_window",
  },
  280: {
    version: 280,
    directory: "empty-compiler-barrier-linux-v280-20260728",
    available: true,
    start_epoch_s: 1785242071,
    end_epoch_s: 1785242416,
    start_iso: "2026-07-28T12:34:31.000Z",
    end_iso: "2026-07-28T12:40:16.000Z",
    duration_minutes: 5.75,
    evidence_kind: "local_artifact_window",
  },
  279: {
    version: 279,
    directory: "goblint-structural-racefree-v279-20260728",
    available: true,
    start_epoch_s: 1785241710,
    end_epoch_s: 1785241888,
    start_iso: "2026-07-28T12:28:30.000Z",
    end_iso: "2026-07-28T12:31:28.000Z",
    duration_minutes: 2.966666666666667,
    evidence_kind: "local_artifact_window",
  },
  278: {
    version: 278,
    directory: "libvsync-atomic-semantics-v278-20260728",
    available: true,
    start_epoch_s: 1785239901,
    end_epoch_s: 1785241365,
    start_iso: "2026-07-28T11:58:21.000Z",
    end_iso: "2026-07-28T12:22:45.000Z",
    duration_minutes: 24.4,
    evidence_kind: "local_and_server_artifact_window",
  },
  277: {
    version: 277,
    directory: "elimination-backoff-native-v277-20260728",
    available: true,
    start_epoch_s: 1785239426,
    end_epoch_s: 1785239722,
    start_iso: "2026-07-28T11:50:26.000Z",
    end_iso: "2026-07-28T11:55:22.000Z",
    duration_minutes: 4.933333333333334,
    evidence_kind: "local_and_server_artifact_window",
  },
  276: {
    version: 276,
    directory: "safestack-relacy-counterexample-v276-20260728",
    available: true,
    start_epoch_s: 1785237696,
    end_epoch_s: 1785239012,
    start_iso: "2026-07-28T11:21:36.000Z",
    end_iso: "2026-07-28T11:43:32.000Z",
    duration_minutes: 21.933333333333334,
    evidence_kind: "local_artifact_window",
  },
  270: {
    version: 270,
    directory: "nested-lifecycle-last-writer-safety-v270-20260728",
    available: true,
    start_epoch_s: 1785227489,
    end_epoch_s: 1785231611,
    start_iso: "2026-07-28T08:31:29.000Z",
    end_iso: "2026-07-28T09:40:11.000Z",
    duration_minutes: 68.7,
    evidence_kind: "local_directory_birth_to_conclusion_mtime",
  },
  269: {
    version: 269,
    directory: "indexed-list-race-safety-v269-20260728",
    available: true,
    start_epoch_s: 1785226245.138962,
    end_epoch_s: 1785227306.600523,
    start_iso: "2026-07-28T08:10:45.138962Z",
    end_iso: "2026-07-28T08:28:26.600523Z",
    duration_minutes: 17.691026016076407,
    evidence_kind: "local_directory_birth_to_conclusion_mtime",
  },
  268: {
    version: 268,
    directory: "indexed-lock-zero-sum-v268-20260728",
    available: true,
    start_epoch_s: 1785223343.621997,
    end_epoch_s: 1785225845.502756,
    start_iso: "2026-07-28T07:22:23.621997Z",
    end_iso: "2026-07-28T08:04:05.502756Z",
    duration_minutes: 41.69801265,
    evidence_kind: "local_directory_birth_to_conclusion_mtime",
  },
  267: {
    version: 267,
    directory: "singleton-function-pointer-zero-sum-v267-20260728",
    available: true,
    start_epoch_s: 1785220458.493014,
    end_epoch_s: 1785223208.92885,
    start_iso: "2026-07-28T06:34:18.493014Z",
    end_iso: "2026-07-28T07:20:08.928850Z",
    duration_minutes: 45.84059726666667,
    evidence_kind: "local_directory_birth_to_conclusion_mtime",
  },
  266: {
    version: 266,
    directory: "mutex-zero-fixedpoint-safety-v266-20260728",
    available: true,
    start_epoch_s: 1785219209.199139,
    end_epoch_s: 1785220124.868951,
    start_iso: "2026-07-28T06:13:29.199139Z",
    end_iso: "2026-07-28T06:28:44.868951Z",
    duration_minutes: 15.261163533333333,
    evidence_kind: "local_directory_birth_to_conclusion_mtime",
  },
  265: {
    version: 265,
    directory: "unwind-progress-logging-demotion-v265-20260728",
    available: true,
    start_epoch_s: 1785218680.512688,
    end_epoch_s: 1785219075.246805,
    start_iso: "2026-07-28T06:04:40.512688Z",
    end_iso: "2026-07-28T06:11:15.246805Z",
    duration_minutes: 6.578901950000001,
    evidence_kind: "local_active_artifact_to_conclusion_mtime",
  },
  264: {
    version: 264,
    directory: "explicit-boolean-lock-protocol-safety-v264-20260728",
    available: true,
    start_epoch_s: 1785169456.476746,
    end_epoch_s: 1785169643.755195,
    start_iso: "2026-07-27T16:24:16.476746Z",
    end_iso: "2026-07-27T16:27:23.755195Z",
    duration_minutes: 3.121307483333333,
    evidence_kind: "local_directory_birth_to_conclusion_mtime",
  },
  263: {
    version: 263,
    directory: "monotone-condition-wait-safety-v263-20260728",
    available: true,
    start_epoch_s: 1785168336,
    end_epoch_s: 1785168729.071931,
    start_iso: "2026-07-27T16:05:36.000Z",
    end_iso: "2026-07-27T16:12:09.072Z",
    duration_minutes: 6.55,
    evidence_kind: "rollout_and_local_server_artifact_window",
  },
  262: {
    version: 262,
    directory: "guard-dominated-common-mutex-safety-v262-20260727",
    available: true,
    start_epoch_s: 1785167503,
    end_epoch_s: 1785167746.647717,
    start_iso: "2026-07-27T15:51:43.000Z",
    end_iso: "2026-07-27T15:55:46.648Z",
    duration_minutes: 4.1,
    evidence_kind: "rollout_and_local_server_artifact_window",
  },
  261: {
    version: 261,
    directory: "wrapped-mutex-zero-sum-safety-v261-20260727",
    available: true,
    start_epoch_s: 1785166910,
    end_epoch_s: 1785167168,
    start_iso: "2026-07-27T15:41:50.000Z",
    end_iso: "2026-07-27T15:46:08.000Z",
    duration_minutes: 4.3,
    evidence_kind: "rollout_and_local_server_artifact_window",
  },
  260: {
    version: 260,
    directory: "independent-object-lock-index-counterexample-v260-20260727",
    available: true,
    start_epoch_s: 1785165901,
    end_epoch_s: 1785166189,
    start_iso: "2026-07-27T15:25:01.000Z",
    end_iso: "2026-07-27T15:29:49.000Z",
    duration_minutes: 4.8,
    evidence_kind: "rollout_and_local_server_artifact_window",
  },
  259: {
    version: 259,
    directory: "cross-slot-list-splice-counterexample-v259-20260727",
    available: true,
    start_epoch_s: 1785164834,
    end_epoch_s: 1785165407,
    start_iso: "2026-07-27T15:07:14.000Z",
    end_iso: "2026-07-27T15:16:47.000Z",
    duration_minutes: 9.55,
    evidence_kind: "rollout_and_local_server_artifact_window",
  },
  258: {
    version: 258,
    directory: "same-slot-different-lock-counterexample-v258-20260727",
    available: true,
    start_epoch_s: 1785163997,
    end_epoch_s: 1785164255,
    start_iso: "2026-07-27T14:53:17.000Z",
    end_iso: "2026-07-27T14:57:35.000Z",
    duration_minutes: 4.3,
    evidence_kind: "rollout_and_local_server_artifact_window",
  },
  257: {
    version: 257,
    directory: "misaligned-index-lock-counterexample-v257-20260727",
    available: true,
    start_epoch_s: 1785163450,
    end_epoch_s: 1785163716,
    start_iso: "2026-07-27T14:44:10.000Z",
    end_iso: "2026-07-27T14:48:36.000Z",
    duration_minutes: 4.433333333333334,
    evidence_kind: "rollout_and_local_server_artifact_window",
  },
  256: {
    version: 256,
    directory: "encoded-race-counterexample-v256-20260727",
    available: true,
    start_epoch_s: 1785162681,
    end_epoch_s: 1785163103,
    start_iso: "2026-07-27T14:31:21.000Z",
    end_iso: "2026-07-27T14:38:23.000Z",
    duration_minutes: 7.033333333333333,
    evidence_kind: "rollout_and_local_server_artifact_window",
  },
  255: {
    version: 255,
    directory: "conserved-sum-nontermination-v255-20260727",
    available: true,
    start_epoch_s: 1785161848,
    end_epoch_s: 1785162219,
    start_iso: "2026-07-27T14:17:28.000Z",
    end_iso: "2026-07-27T14:23:39.000Z",
    duration_minutes: 6.183333333333334,
    evidence_kind: "rollout_and_local_server_artifact_window",
  },
  254: {
    version: 254,
    directory: "isomorphic-modular-fold-pair-v254-20260727",
    available: true,
    start_epoch_s: 1785160726,
    end_epoch_s: 1785161250,
    start_iso: "2026-07-27T13:58:46.000Z",
    end_iso: "2026-07-27T14:07:30.000Z",
    duration_minutes: 8.733333333333333,
    evidence_kind: "rollout_and_local_server_artifact_window",
  },
  253: {
    version: 253,
    directory: "atomic-queue-occupancy-value-v253-20260727",
    available: true,
    start_epoch_s: 1785160075,
    end_epoch_s: 1785160590,
    start_iso: "2026-07-27T13:47:55.000Z",
    end_iso: "2026-07-27T13:56:30.000Z",
    duration_minutes: 8.583333333333334,
    evidence_kind: "rollout_and_local_server_artifact_window",
  },
  252: {
    version: 252,
    directory: "linear-tiled-copy-equivalence-v252-20260727",
    available: true,
    start_epoch_s: 1785158909,
    end_epoch_s: 1785159907,
    start_iso: "2026-07-27T13:28:29.000Z",
    end_iso: "2026-07-27T13:45:07.000Z",
    duration_minutes: 16.633333333333333,
    evidence_kind: "rollout_and_local_server_artifact_window",
  },
  251: {
    version: 251,
    directory: "monotone-chunk-maximum-v251-20260727",
    available: true,
    start_epoch_s: 1785157739,
    end_epoch_s: 1785158055,
    start_iso: "2026-07-27T13:08:59.000Z",
    end_iso: "2026-07-27T13:14:15.000Z",
    duration_minutes: 5.266666666666667,
    evidence_kind: "local_and_server_artifact_window",
  },
  250: {
    version: 250,
    directory: "nonzero-cas-seed-v250-20260727",
    available: true,
    start_epoch_s: 1785157101,
    end_epoch_s: 1785157508,
    start_iso: "2026-07-27T12:58:21.000Z",
    end_iso: "2026-07-27T13:05:08.000Z",
    duration_minutes: 6.783333333333333,
    evidence_kind: "local_and_server_artifact_window",
  },
  249: {
    version: 249,
    directory: "completion-flag-arithmetic-v249-20260727",
    available: true,
    start_epoch_s: 1785156563,
    end_epoch_s: 1785156824,
    start_iso: "2026-07-27T12:49:23.000Z",
    end_iso: "2026-07-27T12:53:44.000Z",
    duration_minutes: 4.35,
    evidence_kind: "local_and_server_artifact_window",
  },
  248: {
    version: 248,
    directory: "finite-two-sided-disjunction-v248-20260727",
    available: true,
    start_epoch_s: 1785156036,
    end_epoch_s: 1785156332,
    start_iso: "2026-07-27T12:40:36.000Z",
    end_iso: "2026-07-27T12:45:32.000Z",
    duration_minutes: 4.933333333333334,
    evidence_kind: "local_and_server_artifact_window",
  },
  247: {
    version: 247,
    directory: "partitioned-count-reduction-v247-20260727",
    available: true,
    start_epoch_s: 1785154828,
    end_epoch_s: 1785155683,
    start_iso: "2026-07-27T12:20:28.000Z",
    end_iso: "2026-07-27T12:34:43.000Z",
    duration_minutes: 14.25,
    evidence_kind: "local_and_server_artifact_window",
  },
  246: {
    version: 246,
    directory: "tls-destructor-counterexample-v246-20260727",
    available: true,
    start_epoch_s: 1785154284,
    end_epoch_s: 1785154634,
    start_iso: "2026-07-27T12:11:24.000Z",
    end_iso: "2026-07-27T12:17:14.000Z",
    duration_minutes: 5.833333333333333,
    evidence_kind: "local_and_server_artifact_window",
  },
  245: {
    version: 245,
    directory: "dynamic-tls-calloc-zero-v245-20260727",
    available: true,
    start_epoch_s: 1785153516,
    end_epoch_s: 1785154046,
    start_iso: "2026-07-27T11:58:36.000Z",
    end_iso: "2026-07-27T12:07:26.000Z",
    duration_minutes: 8.833333333333334,
    evidence_kind: "local_and_server_artifact_window",
  },
  244: {
    version: 244,
    directory: "monotone-potential-overflow-audit-v244-20260727",
    available: true,
    start_epoch_s: 1785153494,
    end_epoch_s: 1785153516,
    start_iso: "2026-07-27T11:58:14.000Z",
    end_iso: "2026-07-27T11:58:36.000Z",
    duration_minutes: 0.36666666666666664,
    evidence_kind: "local_and_server_artifact_window",
  },
  243: {
    version: 243,
    directory: "nonnegative-oscillator-monitor-v243-20260727",
    available: true,
    start_epoch_s: 1785152699,
    end_epoch_s: 1785153342,
    start_iso: "2026-07-27T11:44:59.000Z",
    end_iso: "2026-07-27T11:55:42.000Z",
    duration_minutes: 10.716666666666667,
    evidence_kind: "local_and_server_artifact_window",
  },
  242: {
    version: 242,
    directory: "large-static-complete-unwind-v242-20260727",
    available: true,
    start_epoch_s: 1785152493,
    end_epoch_s: 1785152699,
    start_iso: "2026-07-27T11:41:33.000Z",
    end_iso: "2026-07-27T11:44:59.000Z",
    duration_minutes: 3.433333333333333,
    evidence_kind: "local_and_server_artifact_window",
  },
  241: {
    version: 241,
    directory: "readonly-comparator-algebra-v241-20260727",
    available: true,
    start_epoch_s: 1785150037,
    end_epoch_s: 1785152252,
    start_iso: "2026-07-27T11:00:37.000Z",
    end_iso: "2026-07-27T11:37:32.000Z",
    duration_minutes: 36.916666666666664,
    evidence_kind: "local_and_server_artifact_window",
  },
  240: {
    version: 240,
    directory: "queue-sequence-correspondence-v240-20260727",
    available: true,
    start_epoch_s: 1785147602,
    end_epoch_s: 1785148962,
    start_iso: "2026-07-27T10:20:02.000Z",
    end_iso: "2026-07-27T10:42:42.000Z",
    duration_minutes: 22.666666666666668,
    evidence_kind: "local_and_server_artifact_window",
  },
  239: {
    version: 239,
    directory: "stack-capacity-invariant-v239-20260727",
    available: true,
    start_epoch_s: 1785145392,
    end_epoch_s: 1785147376,
    start_iso: "2026-07-27T09:43:12.000Z",
    end_iso: "2026-07-27T10:16:16.000Z",
    duration_minutes: 33.06666666666667,
    evidence_kind: "local_and_server_artifact_window",
  },
  238: {
    version: 238,
    directory: "post-store-stable-cell-v238-20260727",
    available: true,
    start_epoch_s: 1785142914,
    end_epoch_s: 1785144975,
    start_iso: "2026-07-27T09:01:54.000Z",
    end_iso: "2026-07-27T09:36:15.000Z",
    duration_minutes: 34.35,
    evidence_kind: "local_and_server_artifact_window",
  },
  237: {
    version: 237,
    directory: "index-region-ownership-v237-20260727",
    available: true,
    start_epoch_s: 1785141225,
    end_epoch_s: 1785142635,
    start_iso: "2026-07-27T08:33:45.000Z",
    end_iso: "2026-07-27T08:57:15.000Z",
    duration_minutes: 23.5,
    evidence_kind: "local_artifact_window",
  },
  236: {
    version: 236,
    directory: "mutex-state-call-reachability-v236-20260727",
    available: true,
    start_epoch_s: 1785140943,
    end_epoch_s: 1785141093,
    start_iso: "2026-07-27T08:29:03.000Z",
    end_iso: "2026-07-27T08:31:33.000Z",
    duration_minutes: 2.5,
    evidence_kind: "local_artifact_window",
  },
  235: {
    version: 235,
    directory: "constant-property-discharge-v235-20260727",
    available: true,
    start_epoch_s: 1785140330,
    end_epoch_s: 1785140374,
    start_iso: "2026-07-27T08:18:50.000Z",
    end_iso: "2026-07-27T08:19:34.000Z",
    duration_minutes: 0.7333333333333333,
    evidence_kind: "local_artifact_window",
  },
  234: {
    version: 234,
    directory: "ticket-lock-dispatch-v234-20260727",
    available: true,
    start_epoch_s: 1785139338.175,
    end_epoch_s: 1785139970.7812457,
    start_iso: "2026-07-27T08:02:18.175Z",
    end_iso: "2026-07-27T08:12:50.781Z",
    duration_minutes: 10.543437429269154,
    evidence_kind: "rollout_and_local_artifact_window",
  },
  233: {
    version: 233,
    directory: "ticket-lock-ownership-v233-20260727",
    available: true,
    start_epoch_s: 1785137498.911,
    end_epoch_s: 1785139028.882,
    start_iso: "2026-07-27T07:31:38.911Z",
    end_iso: "2026-07-27T07:57:08.882Z",
    duration_minutes: 25.499516665935516,
    evidence_kind: "rollout_and_local_artifact_window",
  },
  232: {
    version: 232,
    directory: "pthread-ext-residual-v232-20260727",
    available: true,
    start_epoch_s: 1785136976,
    end_epoch_s: 1785137136,
    start_iso: "2026-07-27T07:22:56.000Z",
    end_iso: "2026-07-27T07:25:36.000Z",
    duration_minutes: 2.6666666666666665,
    evidence_kind: "local_artifact_mtime_window",
  },
  231: {
    version: 231,
    directory: "queue-stack-bound401-v231-20260727",
    available: true,
    start_epoch_s: 1785136623,
    end_epoch_s: 1785136865,
    start_iso: "2026-07-27T07:17:03.000Z",
    end_iso: "2026-07-27T07:21:05.000Z",
    duration_minutes: 4.033333333333333,
    evidence_kind: "local_artifact_mtime_window",
  },
  230: {
    version: 230,
    directory: "remaining-unknown-mechanism-census-v230-20260727",
    available: true,
    start_epoch_s: 1785135953,
    end_epoch_s: 1785136510,
    start_iso: "2026-07-27T07:05:53.000Z",
    end_iso: "2026-07-27T07:15:10.000Z",
    duration_minutes: 9.283333333333333,
    evidence_kind: "local_artifact_mtime_window",
  },
  229: {
    version: 229,
    directory: "libvsync-indexed-lifecycle-v229-20260727",
    available: true,
    start_epoch_s: 1785133832,
    end_epoch_s: 1785135212,
    start_iso: "2026-07-27T06:30:32.000Z",
    end_iso: "2026-07-27T06:53:32.000Z",
    duration_minutes: 23,
    evidence_kind: "local_artifact_mtime_window",
  },
  220: {
    version: 220,
    directory: "delta-cube-fixedpoint-worklist-v220-20260727",
    available: true,
    start_epoch_s: 1785119883,
    end_epoch_s: 1785122300.9348853,
    start_iso: "2026-07-27T02:38:03.000Z",
    end_iso: "2026-07-27T03:18:20.934Z",
    duration_minutes: 40.298914754390715,
    evidence_kind: "server_artifact_mtime_window",
  },
  221: {
    version: 221,
    directory: "post-affine-residual-attribution-v221-20260727",
    available: true,
    start_epoch_s: 1785122767,
    end_epoch_s: 1785123869,
    start_iso: "2026-07-27T03:26:07.000Z",
    end_iso: "2026-07-27T03:44:29.000Z",
    duration_minutes: 18.366666666666667,
    evidence_kind: "local_artifact_mtime_window",
  },
  222: {
    version: 222,
    directory: "single-process-combined-proof-v222-20260727",
    available: true,
    start_epoch_s: 1785124271,
    end_epoch_s: 1785128197,
    start_iso: "2026-07-27T03:51:11.000Z",
    end_iso: "2026-07-27T04:56:37.000Z",
    duration_minutes: 65.43333333333334,
    evidence_kind: "local_artifact_mtime_window",
  },
  223: {
    version: 223,
    directory: "final-native-residual-v223-20260727",
    available: true,
    start_epoch_s: 1785128456,
    end_epoch_s: 1785128733,
    start_iso: "2026-07-27T05:00:56.000Z",
    end_iso: "2026-07-27T05:05:33.000Z",
    duration_minutes: 4.616666666666666,
    evidence_kind: "local_artifact_mtime_window",
  },
  224: {
    version: 224,
    directory: "native-atomic-affine-v224-20260727",
    available: true,
    start_epoch_s: 1785128754,
    end_epoch_s: 1785128939,
    start_iso: "2026-07-27T05:05:54.000Z",
    end_iso: "2026-07-27T05:08:59.000Z",
    duration_minutes: 3.0833333333333335,
    evidence_kind: "local_artifact_mtime_window",
  },
  225: {
    version: 225,
    directory: "finite-constant-protocol-product-v225-20260727",
    available: true,
    start_epoch_s: 1785129356,
    end_epoch_s: 1785131295,
    start_iso: "2026-07-27T05:15:56.000Z",
    end_iso: "2026-07-27T05:48:15.000Z",
    duration_minutes: 32.31666666666667,
    evidence_kind: "local_artifact_mtime_window",
  },
  226: {
    version: 226,
    directory: "preprocessed-atomic-dispatch-v226-20260727",
    available: true,
    start_epoch_s: 1785131295,
    end_epoch_s: 1785131691,
    start_iso: "2026-07-27T05:48:15.000Z",
    end_iso: "2026-07-27T05:54:51.000Z",
    duration_minutes: 6.6,
    evidence_kind: "local_artifact_mtime_window",
  },
  228: {
    version: 228,
    directory: "large-static-unwind-rescue-v228-20260727",
    available: true,
    start_epoch_s: 1785133209,
    end_epoch_s: 1785133598,
    start_iso: "2026-07-27T06:20:09.000Z",
    end_iso: "2026-07-27T06:26:38.000Z",
    duration_minutes: 6.483333333333333,
    evidence_kind: "local_artifact_mtime_window",
  },
  227: {
    version: 227,
    directory: "weaver-residual-semantic-audit-v227-20260727",
    available: true,
    start_epoch_s: 1785132091,
    end_epoch_s: 1785132960,
    start_iso: "2026-07-27T06:01:31.000Z",
    end_iso: "2026-07-27T06:16:00.000Z",
    duration_minutes: 14.483333333333333,
    evidence_kind: "local_artifact_mtime_window",
  },
  196: {
    version: 196,
    directory: "dynamic-initialization-rf-v196-20260727",
    available: true,
    start_epoch_s: 1785087411,
    end_epoch_s: 1785092195,
    start_iso: "2026-07-26T17:36:51.000Z",
    end_iso: "2026-07-26T18:56:35.000Z",
    duration_minutes: 79.73333333333333,
    evidence_kind: "local_directory_birth_to_table_mtime",
    file_count: 1585,
    raw_start_path:
      "/Users/sujie/Documents/Codes/C++/Deagle/experiments/dynamic-initialization-rf-v196-20260727",
    raw_end_path:
      "/Users/sujie/Documents/Codes/C++/Deagle/experiments/dynamic-initialization-rf-v196-20260727/full-v196-results/results/full-v196.html",
  },
  197: {
    version: 197,
    directory: "dynamic-object-candidate-guards-v197-20260727",
    available: true,
    start_epoch_s: 1785092523,
    end_epoch_s: 1785093173,
    start_iso: "2026-07-26T19:02:03.000Z",
    end_iso: "2026-07-26T19:12:53.000Z",
    duration_minutes: 10.833333333333334,
    evidence_kind: "local_directory_birth_to_conclusion_mtime",
    file_count: 803,
    raw_start_path:
      "/Users/sujie/Documents/Codes/C++/Deagle/experiments/dynamic-object-candidate-guards-v197-20260727",
    raw_end_path:
      "/Users/sujie/Documents/Codes/C++/Deagle/experiments/dynamic-object-candidate-guards-v197-20260727/task_plan.md",
  },
  198: {
    version: 198,
    directory: "multitarget-dereference-guards-v198-20260727",
    available: true,
    start_epoch_s: 1785093334,
    end_epoch_s: 1785093617,
    start_iso: "2026-07-26T19:15:34.000Z",
    end_iso: "2026-07-26T19:20:17.000Z",
    duration_minutes: 4.716666666666667,
    evidence_kind: "local_directory_birth_to_conclusion_mtime",
    file_count: 58,
    raw_start_path:
      "/Users/sujie/Documents/Codes/C++/Deagle/experiments/multitarget-dereference-guards-v198-20260727",
    raw_end_path:
      "/Users/sujie/Documents/Codes/C++/Deagle/experiments/multitarget-dereference-guards-v198-20260727/task_plan.md",
  },
  199: {
    version: 199,
    directory: "conditional-event-generation-v199-20260727",
    available: true,
    start_epoch_s: 1785093866,
    end_epoch_s: 1785094736,
    start_iso: "2026-07-26T19:24:26.000Z",
    end_iso: "2026-07-26T19:38:56.000Z",
    duration_minutes: 14.5,
    evidence_kind: "local_directory_birth_to_conclusion_mtime",
    file_count: 814,
    raw_start_path:
      "/Users/sujie/Documents/Codes/C++/Deagle/experiments/conditional-event-generation-v199-20260727",
    raw_end_path:
      "/Users/sujie/Documents/Codes/C++/Deagle/experiments/conditional-event-generation-v199-20260727/task_plan.md",
  },
  200: {
    version: 200,
    directory: "dereference-local-event-guards-v200-20260727",
    available: true,
    start_epoch_s: 1785095023,
    end_epoch_s: 1785096578,
    start_iso: "2026-07-26T19:43:43.000Z",
    end_iso: "2026-07-26T20:09:38.000Z",
    duration_minutes: 25.916666666666668,
    evidence_kind: "local_directory_birth_to_conclusion_mtime",
    file_count: 810,
    raw_start_path:
      "/Users/sujie/Documents/Codes/C++/Deagle/experiments/dereference-local-event-guards-v200-20260727",
    raw_end_path:
      "/Users/sujie/Documents/Codes/C++/Deagle/experiments/dereference-local-event-guards-v200-20260727/task_plan.md",
  },
  201: {
    version: 201,
    directory: "guard-conflict-rf-pruning-v201-20260727",
    available: true,
    start_epoch_s: 1785097051,
    end_epoch_s: 1785097255,
    start_iso: "2026-07-26T20:17:31.000Z",
    end_iso: "2026-07-26T20:20:55.000Z",
    duration_minutes: 3.4,
    evidence_kind: "local_directory_birth_to_conclusion_mtime",
    file_count: 62,
    raw_start_path:
      "/Users/sujie/Documents/Codes/C++/Deagle/experiments/guard-conflict-rf-pruning-v201-20260727",
    raw_end_path:
      "/Users/sujie/Documents/Codes/C++/Deagle/experiments/guard-conflict-rf-pruning-v201-20260727/task_plan.md",
  },
  202: {
    version: 202,
    directory: "latest-local-write-rf-dominance-v202-20260727",
    available: true,
    start_epoch_s: 1785097440,
    end_epoch_s: 1785098324,
    start_iso: "2026-07-26T20:24:00.000Z",
    end_iso: "2026-07-26T20:38:44.000Z",
    duration_minutes: 14.733333333333333,
    evidence_kind: "local_directory_birth_to_conclusion_mtime",
    file_count: 57,
    raw_start_path:
      "/Users/sujie/Documents/Codes/C++/Deagle/experiments/latest-local-write-rf-dominance-v202-20260727",
    raw_end_path:
      "/Users/sujie/Documents/Codes/C++/Deagle/experiments/latest-local-write-rf-dominance-v202-20260727/task_plan.md",
  },
  203: {
    version: 203,
    directory: "property-relevant-event-cone-v203-20260727",
    available: true,
    start_epoch_s: 1785098850,
    end_epoch_s: 1785101452,
    start_iso: "2026-07-26T20:47:30.000Z",
    end_iso: "2026-07-26T21:30:52.000Z",
    duration_minutes: 43.36666666666667,
    evidence_kind: "server_artifact_mtime_window",
    file_count: 1545,
    raw_start_path:
      "/data3/sujie/experiments/property-relevant-event-cone-v203-20260727/results.md",
    raw_end_path:
      "/data3/sujie/experiments/property-relevant-event-cone-v203-20260727/analysis-output/full-analysis.json",
  },
  204: {
    version: 204,
    directory: "synchronization-relevance-closure-v204-20260727",
    available: true,
    start_epoch_s: 1785102114,
    end_epoch_s: 1785102186,
    start_iso: "2026-07-26T21:41:54.000Z",
    end_iso: "2026-07-26T21:43:06.000Z",
    duration_minutes: 1.2,
    evidence_kind: "server_artifact_mtime_window",
    file_count: 9,
    raw_start_path:
      "/data3/sujie/experiments/synchronization-relevance-closure-v204-20260727/analyze_residual_sync.py",
    raw_end_path:
      "/data3/sujie/experiments/synchronization-relevance-closure-v204-20260727/task_plan.md",
  },
  205: {
    version: 205,
    directory: "residual-early-stage-attribution-v205-20260727",
    available: true,
    start_epoch_s: 1785102358,
    end_epoch_s: 1785102797,
    start_iso: "2026-07-26T21:45:58.000Z",
    end_iso: "2026-07-26T21:53:17.000Z",
    duration_minutes: 7.316666666666666,
    evidence_kind: "server_artifact_mtime_window",
    file_count: 49,
    raw_start_path:
      "/data3/sujie/experiments/residual-early-stage-attribution-v205-20260727/classify_unresolved.py",
    raw_end_path:
      "/data3/sujie/experiments/residual-early-stage-attribution-v205-20260727/profile-analysis/summary.json",
  },
  206: {
    version: 206,
    directory: "thread-modular-loop-certificate-v206-20260727",
    available: true,
    start_epoch_s: 1785103108,
    end_epoch_s: 1785105595,
    start_iso: "2026-07-26T21:58:28.000Z",
    end_iso: "2026-07-26T22:39:55.000Z",
    duration_minutes: 41.45,
    evidence_kind: "server_artifact_mtime_window",
    file_count: 161,
    raw_start_path:
      "/data3/sujie/experiments/thread-modular-loop-certificate-v206-20260727/expected.md",
    raw_end_path:
      "/data3/sujie/experiments/thread-modular-loop-certificate-v206-20260727/task_plan.md",
  },
  207: {
    version: 207,
    directory: "interference-wp-predicate-closure-v207-20260727",
    available: true,
    start_epoch_s: 1785105846,
    end_epoch_s: 1785106497,
    start_iso: "2026-07-26T22:44:06.000Z",
    end_iso: "2026-07-26T22:54:57.000Z",
    duration_minutes: 10.85,
    evidence_kind: "server_artifact_mtime_window",
    file_count: 19,
    raw_start_path:
      "/data3/sujie/experiments/interference-wp-predicate-closure-v207-20260727/expected.md",
    raw_end_path:
      "/data3/sujie/experiments/interference-wp-predicate-closure-v207-20260727/task_plan.md",
  },
  208: {
    version: 208,
    directory: "property-seeded-wp-refinement-v208-20260727",
    available: true,
    start_epoch_s: 1785106643,
    end_epoch_s: 1785106909,
    start_iso: "2026-07-26T22:57:23.000Z",
    end_iso: "2026-07-26T23:01:49.000Z",
    duration_minutes: 4.433333333333334,
    evidence_kind: "server_artifact_mtime_window",
    file_count: 12,
    raw_start_path:
      "/data3/sujie/experiments/property-seeded-wp-refinement-v208-20260727/expected.md",
    raw_end_path:
      "/data3/sujie/experiments/property-seeded-wp-refinement-v208-20260727/task_plan.md",
  },
  209: {
    version: 209,
    directory: "wp-origin-proof-core-v209-20260727",
    available: true,
    start_epoch_s: 1785106984,
    end_epoch_s: 1785107710,
    start_iso: "2026-07-26T23:03:04.000Z",
    end_iso: "2026-07-26T23:15:10.000Z",
    duration_minutes: 12.1,
    evidence_kind: "server_artifact_mtime_window",
    file_count: 22,
    raw_start_path:
      "/data3/sujie/experiments/wp-origin-proof-core-v209-20260727/expected.md",
    raw_end_path:
      "/data3/sujie/experiments/wp-origin-proof-core-v209-20260727/variant-spec.md",
  },
  210: {
    version: 210,
    directory: "wp-seed-origin-replication-v210-20260727",
    available: true,
    start_epoch_s: 1785107777,
    end_epoch_s: 1785108480,
    start_iso: "2026-07-26T23:16:17.000Z",
    end_iso: "2026-07-26T23:28:00.000Z",
    duration_minutes: 11.716666666666667,
    evidence_kind: "server_artifact_mtime_window",
    file_count: 36,
    raw_start_path:
      "/data3/sujie/experiments/wp-seed-origin-replication-v210-20260727/expected.md",
    raw_end_path:
      "/data3/sujie/experiments/wp-seed-origin-replication-v210-20260727/task_plan.md",
  },
  211: {
    version: 211,
    directory: "cyclic-goto-wp-refinement-v211-20260727",
    available: true,
    start_epoch_s: 1785108594,
    end_epoch_s: 1785108899,
    start_iso: "2026-07-26T23:29:54.000Z",
    end_iso: "2026-07-26T23:34:59.000Z",
    duration_minutes: 5.083333333333333,
    evidence_kind: "server_artifact_mtime_window",
    file_count: 28,
    raw_start_path:
      "/data3/sujie/experiments/cyclic-goto-wp-refinement-v211-20260727/expected.md",
    raw_end_path:
      "/data3/sujie/experiments/cyclic-goto-wp-refinement-v211-20260727/task_plan.md",
  },
  212: {
    version: 212,
    directory: "property-overlap-goto-wp-v212-20260727",
    available: true,
    start_epoch_s: 1785109053,
    end_epoch_s: 1785109351,
    start_iso: "2026-07-26T23:37:33.000Z",
    end_iso: "2026-07-26T23:42:31.000Z",
    duration_minutes: 4.966666666666667,
    evidence_kind: "server_artifact_mtime_window",
    file_count: 28,
    raw_start_path:
      "/data3/sujie/experiments/property-overlap-goto-wp-v212-20260727/expected.md",
    raw_end_path:
      "/data3/sujie/experiments/property-overlap-goto-wp-v212-20260727/task_plan.md",
  },
  213: {
    version: 213,
    directory: "error-control-goto-wp-v213-20260727",
    available: true,
    start_epoch_s: 1785109442,
    end_epoch_s: 1785109716,
    start_iso: "2026-07-26T23:44:02.000Z",
    end_iso: "2026-07-26T23:48:36.000Z",
    duration_minutes: 4.566666666666666,
    evidence_kind: "server_artifact_mtime_window",
    file_count: 28,
    raw_start_path:
      "/data3/sujie/experiments/error-control-goto-wp-v213-20260727/expected.md",
    raw_end_path:
      "/data3/sujie/experiments/error-control-goto-wp-v213-20260727/task_plan.md",
  },
  214: {
    version: 214,
    directory: "error-control-wp-depth-v214-20260727",
    available: true,
    start_epoch_s: 1785109824,
    end_epoch_s: 1785110111,
    start_iso: "2026-07-26T23:50:24.000Z",
    end_iso: "2026-07-26T23:55:11.000Z",
    duration_minutes: 4.783333333333333,
    evidence_kind: "server_artifact_mtime_window",
    file_count: 31,
    raw_start_path:
      "/data3/sujie/experiments/error-control-wp-depth-v214-20260727/expected.md",
    raw_end_path:
      "/data3/sujie/experiments/error-control-wp-depth-v214-20260727/task_plan.md",
  },
  215: {
    version: 215,
    directory: "error-control-depth2-natural-v215-20260727",
    available: true,
    start_epoch_s: 1785110201,
    end_epoch_s: 1785110505,
    start_iso: "2026-07-26T23:56:41.000Z",
    end_iso: "2026-07-27T00:01:45.000Z",
    duration_minutes: 5.066666666666666,
    evidence_kind: "server_artifact_mtime_window",
    file_count: 17,
    raw_start_path:
      "/data3/sujie/experiments/error-control-depth2-natural-v215-20260727/expected.md",
    raw_end_path:
      "/data3/sujie/experiments/error-control-depth2-natural-v215-20260727/task_plan.md",
  },
  216: {
    version: 216,
    directory: "relational-proof-gap-audit-v216-20260727",
    available: true,
    start_epoch_s: 1785110760,
    end_epoch_s: 1785111425,
    start_iso: "2026-07-27T00:06:00.000Z",
    end_iso: "2026-07-27T00:17:05.000Z",
    duration_minutes: 11.083333333333334,
    evidence_kind: "server_artifact_mtime_window",
    file_count: 25,
    raw_start_path:
      "/data3/sujie/experiments/relational-proof-gap-audit-v216-20260727/expected.md",
    raw_end_path:
      "/data3/sujie/experiments/relational-proof-gap-audit-v216-20260727/task_plan.md",
  },
  217: {
    version: 217,
    directory: "guarded-affine-transition-certificate-v217-20260727",
    available: true,
    start_epoch_s: 1785111577,
    end_epoch_s: 1785117082,
    start_iso: "2026-07-27T00:19:37.000Z",
    end_iso: "2026-07-27T01:51:22.000Z",
    duration_minutes: 91.75,
    evidence_kind: "server_artifact_mtime_window",
    file_count: 205,
    raw_start_path:
      "/data3/sujie/experiments/guarded-affine-transition-certificate-v217-20260727/expected.md",
    raw_end_path:
      "/data3/sujie/experiments/guarded-affine-transition-certificate-v217-20260727/workspace-restored-sha256.txt",
  },
  218: {
    version: 218,
    directory: "integrated-affine-dispatch-v218-20260727",
    available: true,
    start_epoch_s: 1785117473,
    end_epoch_s: 1785119111,
    start_iso: "2026-07-27T01:57:53.000Z",
    end_iso: "2026-07-27T02:25:11.000Z",
    duration_minutes: 27.3,
    evidence_kind: "server_artifact_mtime_window",
    file_count: 932,
    raw_start_path:
      "/data3/sujie/experiments/integrated-affine-dispatch-v218-20260727/setup-sha256.txt",
    raw_end_path:
      "/data3/sujie/experiments/integrated-affine-dispatch-v218-20260727/workspace-restored-sha256.txt",
  },
  219: {
    version: 219,
    directory: "affine-only-fail-closed-v219-20260727",
    available: true,
    start_epoch_s: 1785119512,
    end_epoch_s: 1785119579,
    start_iso: "2026-07-27T02:31:52.000Z",
    end_iso: "2026-07-27T02:32:59.000Z",
    duration_minutes: 1.1166666666666667,
    evidence_kind: "server_artifact_mtime_window",
    file_count: 5,
    raw_start_path:
      "/data3/sujie/experiments/affine-only-fail-closed-v219-20260727/expected.md",
    raw_end_path:
      "/data3/sujie/experiments/affine-only-fail-closed-v219-20260727/task_plan.md",
  },
};

const preferredDirectories = {
  2: "watched-cofr-event-driven-shadow-v2-20260722",
  3: "watched-cofr-event-driven-diagnostic-v3-20260722",
  129: "cas-linearization-stability-audit-v129-20260724",
};

const rows = [
  {
    version: 0,
    label: "Baseline",
    method: "Pristine cloned Deagle",
    status: "baseline",
    scope: "exact725",
    description:
      "The first-clone Deagle control run: 725 tasks, 48 workers, 1 core and 4 GB per task, 60-second limit.",
    source: "source-records/shallow-counterexample-full-v46-20260723/conclusion.md",
    timing: {
      available: false,
      reason: "baseline_is_not_an_optimization_version",
    },
    memory_sum_source: memorySumEvidence.get(0).source_xml,
    metrics: {
      correct: exactOverrides[0].correct,
      cpu_s: exactOverrides[0].cpu,
      wall_s: exactOverrides[0].wall,
      memory_sum_b: memorySumOverrides[0],
      paired_memory_delta_pct: 0,
    },
  },
];

for (let version = 1; version <= 296; ++version) {
  const directories = directoriesByVersion.get(version) || [];
  const primary =
    preferredDirectories[version] ||
    directories.find((directory) => directory !== "v129-vs-pristine-reuse-20260724") ||
    null;
  if (primary === null) {
    const timing = versionTimes.get(version) || {
      available: false,
      reason: "no_timestamp_record",
    };
    rows.push({
      version,
      label: `V${version}`,
      method: "No independent experiment record",
      status: "missing",
      scope: "missing",
      description:
        "No independent experiment directory or version-specific record was found in the preserved server snapshot.",
      source: null,
      source_notes: null,
      memory_sum_source: null,
      timing,
      metrics: {
        correct: null,
        cpu_s: null,
        wall_s: null,
        memory_sum_b: null,
        paired_memory_delta_pct: null,
      },
      extracted_evidence: {},
      exact_override: false,
    });
    continue;
  }
  let conclusion = readIfExists(path.join(recordsRoot, primary, "conclusion.md"));
  let notes = readIfExists(path.join(recordsRoot, primary, "notes.md"));
  const localCandidates = localExperimentsRoots.flatMap((root) =>
    fs
      .readdirSync(root)
      .filter((directory) => lastVersion(directory) === version)
  );
  if (localCandidates.length) {
    const localPrimary = localCandidates.includes(primary)
      ? primary
      : localCandidates[0];
    const localRoot = localExperimentsRoots.find((root) =>
      fs.existsSync(path.join(root, localPrimary))
    );
    const local = path.join(localRoot, localPrimary);
    conclusion = readIfExists(path.join(local, "conclusion.md")) || conclusion;
    notes = readIfExists(path.join(local, "notes.md")) || notes;
  }
  if (version === 129) {
    conclusion +=
      "\n\n" +
      readIfExists(
        path.join(
          recordsRoot,
          "v129-vs-pristine-reuse-20260724",
          "conclusion.md"
        )
      );
  }
  const text = `${conclusion}\n${notes}`;
  const correct = chooseCorrect(text);
  const cpu = chooseSeconds(text, "cpu");
  const wall = chooseSeconds(text, "wall");
  const peak = choosePeakMemory(text);
  const memory = chooseMemoryDelta(text);
  const exact = exactOverrides[version];
  const memoryEvidence = memorySumEvidence.get(version) || null;
  if (
    exact &&
    !nativeRedoVersions.has(version) &&
    (!memoryEvidence ||
      memoryEvidence.memory_sum_b !== memorySumOverrides[version])
  )
    throw new Error(`missing or inconsistent memory-sum evidence for V${version}`);
  const timing = timingOverrides[version] || versionTimes.get(version) || {
    available: false,
    reason: "no_timestamp_record",
  };
  const status =
    statusOverrides[version] || classify(`${conclusion}\n${notes}`);
  const hasExact = Boolean(exact);
  const normalizedStatus =
    status === "successful" && !hasExact ? "audit" : status;
  const wrapperOnly = wrapperOnlyVersions.has(version);
  const rawCorrect =
    adjudicatedCorrectOverrides[version] ?? exact?.correct ?? null;

  rows.push({
    version,
    label: `V${version}`,
    method: methodOverrides[version] || humanize(primary),
    status: normalizedStatus,
    scope: wrapperOnly
      ? "wrapper_certificate_only"
      : hasExact
        ? "exact725"
        : "target_or_audit",
    contribution_class: wrapperOnly
      ? "wrapper_certificate_only_pending_native_redo"
      : nativeRedoVersions.has(version)
        ? version >= 258
          ? "native_redo"
          : "native_consolidated_redo"
        : "verifier_or_audit",
    description: wrapperOnly
      ? "Wrapper-only certificate evidence; not counted as a Deagle verifier contribution. Native redo is required. Historical result: " +
        (descriptionOverrides[version] ||
          firstEvidenceParagraph(conclusion || notes))
      : descriptionOverrides[version] ||
        firstEvidenceParagraph(conclusion || notes),
    source: fs.existsSync(path.join(recordsRoot, primary))
      ? `source-records/${primary}/conclusion.md`
      : `../../experiments/${primary}/conclusion.md`,
    source_notes: fs.existsSync(path.join(recordsRoot, primary))
      ? `source-records/${primary}/notes.md`
      : `../../experiments/${primary}/notes.md`,
    memory_sum_source: nativeRedoVersions.has(version)
      ? nativeRedoMemorySources[version]
      : memoryEvidence?.source_xml ?? null,
    ...([291, 294, 295, 296].includes(version)
      ? {
          comparison_protocol_override: {
          tasks: 725,
          workers: 8,
          cores_per_task: 1,
          memory_per_task_gb: 4,
          time_limit_s: 60,
          paired_baseline_version:
            version === 291
              ? 290
              : version === 294
                ? 291
                : version - 1,
          },
          resource_comparable_with_historical_trend: false,
        }
      : {}),
    timing,
    metrics: {
      correct: wrapperOnly ? null : rawCorrect,
      cpu_s: wrapperOnly ? null : exact?.cpu ?? null,
      wall_s: wrapperOnly ? null : exact?.wall ?? null,
      memory_sum_b: wrapperOnly
        ? null
        : memorySumOverrides[version] ?? null,
      paired_memory_delta_pct:
        wrapperOnly ? null : memoryDeltaOverrides[version] ?? null,
    },
    wrapper_metrics: wrapperEvidenceVersions.has(version)
      ? wrapperMetricOverrides[version] || {
          correct: rawCorrect,
          cpu_s: exact?.cpu ?? null,
          wall_s: exact?.wall ?? null,
          memory_sum_b: memorySumOverrides[version] ?? null,
        }
      : null,
    extracted_evidence: {
      correct: correct?.evidence ?? null,
      cpu: cpu?.evidence ?? null,
      wall: wall?.evidence ?? null,
      peak_memory: peak?.evidence ?? null,
      paired_memory: memory?.evidence ?? null,
    },
    exact_override: hasExact && !wrapperOnly,
    wrapper_exact_evidence: hasExact && wrapperEvidenceVersions.has(version),
  });
}

const baseline = rows[0].metrics;
let previousSuccessful = rows[0];
for (const row of rows) {
  const metrics = row.metrics;
  metrics.correct_vs_baseline = metrics.correct == null
    ? null
    : metrics.correct - baseline.correct;
  metrics.cpu_vs_baseline_pct = metrics.cpu_s == null
    ? null
    : ((metrics.cpu_s / baseline.cpu_s) - 1) * 100;
  metrics.wall_vs_baseline_pct = metrics.wall_s == null
    ? null
    : ((metrics.wall_s / baseline.wall_s) - 1) * 100;
  metrics.memory_sum_vs_baseline_pct = metrics.memory_sum_b == null
    ? null
    : ((metrics.memory_sum_b / baseline.memory_sum_b) - 1) * 100;
  if (row.resource_comparable_with_historical_trend === false) {
    metrics.cpu_vs_baseline_pct = null;
    metrics.wall_vs_baseline_pct = null;
    metrics.memory_sum_vs_baseline_pct = null;
  }
  if (row.version !== 0 && row.scope === "exact725") {
    const previous = previousSuccessful.metrics;
    metrics.correct_vs_previous_success = metrics.correct - previous.correct;
    metrics.cpu_vs_previous_success_pct =
      ((metrics.cpu_s / previous.cpu_s) - 1) * 100;
    metrics.wall_vs_previous_success_pct =
      ((metrics.wall_s / previous.wall_s) - 1) * 100;
    if (row.resource_comparable_with_historical_trend === false) {
      metrics.cpu_vs_previous_success_pct = null;
      metrics.wall_vs_previous_success_pct = null;
    }
  } else {
    metrics.correct_vs_previous_success = null;
    metrics.cpu_vs_previous_success_pct = null;
    metrics.wall_vs_previous_success_pct = null;
  }
  if (row.status === "successful" && row.scope === "exact725")
    previousSuccessful = row;
}

const output = {
  generated_at: new Date().toISOString(),
  comparison_protocol: {
    tasks: 725,
    workers: 48,
    cores_per_task: 1,
    memory_per_task_gb: 4,
    time_limit_s: 60,
    rounds: 1,
  },
  caveats: [
    "Most full-suite configurations were run once; the dashboard is descriptive, not an inferential significance analysis.",
    "Missing exact725 metrics mean no comparable full run was authorized or preserved; missing values are not zeros.",
    "Total memory is the sum of BenchExec's per-task peak-memory measurements over all 725 tasks; it is an aggregate benchmark footprint, not simultaneous RAM usage.",
    "Paired per-task geometric-mean memory change is retained as a secondary distribution-sensitive view; it is not substituted for total memory.",
    "Optimization duration is an artifact-backed observed wall-clock interval covering research, implementation, experiments, analysis, and documentation; it is not pure model-compute time.",
    "V17-V20 and V168 share timestamp records with another version, while V37 and V91 lack independent records; their durations remain missing rather than being estimated.",
    "Some historical controls were reused across dates; cumulative baseline comparisons are useful for progress, not precise per-version causal attribution.",
    "V291 and V294-V296 were measured after a server restart with 8 physical workers. Their coverage and resource claims use contemporaneous N8 paired controls; their raw totals are shown in the ledger but excluded from the historical 48-worker resource trend lines.",
  ],
  rows,
};

fs.writeFileSync(
  path.join(here, "optimization-impact-data.json"),
  JSON.stringify(output, null, 2) + "\n"
);

const csvFields = [
  "version",
  "label",
  "method",
  "status",
  "scope",
  "correct",
  "cpu_s",
  "wall_s",
  "memory_sum_b",
  "paired_memory_delta_pct",
  "optimization_start",
  "optimization_end",
  "optimization_duration_minutes",
  "correct_vs_baseline",
  "cpu_vs_baseline_pct",
  "wall_vs_baseline_pct",
  "source",
];
const escapeCsv = (value) => {
  if (value === null || value === undefined) return "";
  const string = String(value);
  return /[",\n]/.test(string) ? `"${string.replace(/"/g, '""')}"` : string;
};
const csv = [
  csvFields.join(","),
  ...rows.map((row) =>
    csvFields
      .map((field) => {
        const value =
          field === "optimization_start"
            ? row.timing.start_iso
            : field === "optimization_end"
              ? row.timing.end_iso
              : field === "optimization_duration_minutes"
                ? row.timing.duration_minutes
                : field in row
                  ? row[field]
                  : row.metrics[field];
        return escapeCsv(value);
      })
      .join(",")
  ),
].join("\n");
fs.writeFileSync(path.join(here, "optimization-impact-data.csv"), csv + "\n");

// The standalone file:// dashboard embeds the JSON snapshot. Rebuild it in
// the same command so data and the page cannot silently drift apart.
execFileSync(
  process.execPath,
  [path.join(here, "build-dashboard-html.js")],
  { stdio: "inherit" }
);

console.log(
  JSON.stringify(
    {
      rows: rows.length,
      successful: rows.filter((row) => row.status === "successful").length,
      failed: rows.filter((row) => row.status === "failed").length,
      audit: rows.filter((row) => row.status === "audit").length,
      exact725: rows.filter((row) => row.scope === "exact725").length,
    },
    null,
    2
  )
);
