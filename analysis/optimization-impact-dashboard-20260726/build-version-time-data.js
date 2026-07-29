#!/usr/bin/env node

const fs = require("fs");
const path = require("path");

const here = __dirname;
const input = process.argv[2];
if (!input || !fs.existsSync(input)) {
  throw new Error("usage: build-version-time-data.js <remote-time-audit.txt>");
}

const records = new Map();
for (const line of fs.readFileSync(input, "utf8").trim().split("\n")) {
  const parts = line.split("|");
  const version = Number(parts[0]);
  if (!Number.isInteger(version)) continue;
  if (parts[2] === "MISSING") {
    records.set(version, {
      version,
      directory: parts[1],
      available: false,
      reason: "experiment_directory_missing",
    });
    continue;
  }
  records.set(version, {
    version,
    directory: parts[1],
    file_count: Number(parts[2]),
    raw_start_epoch_s: Number(parts[3]),
    raw_start_path: parts[4],
    raw_end_epoch_s: Number(parts[5]),
    raw_end_path: parts.slice(6).join("|"),
  });
}

// These versions do not have independently timestamped experiment records.
// Their evidence was recovered from one shared note/directory, so splitting
// the elapsed interval among them would invent precision.
const sharedRecordVersions = new Set([17, 18, 19, 20, 168]);
let previousEnd = null;
const rows = [];

for (let version = 1; version <= 204; ++version) {
  const record = records.get(version);
  if (!record) {
    rows.push({
      version,
      available: false,
      reason: "no_independent_experiment_record",
    });
    continue;
  }
  if (sharedRecordVersions.has(version)) {
    rows.push({
      version,
      directory: record.directory,
      available: false,
      reason: "shared_record_cannot_be_split_by_version",
      raw_start_epoch_s: record.raw_start_epoch_s,
      raw_end_epoch_s: record.raw_end_epoch_s,
    });
    continue;
  }

  // Copied controls, inherited helper files, and restored source snapshots can
  // predate the version. The remote audit excludes the obvious copies; this
  // monotone clamp removes any remaining inherited timestamp that is older
  // than the end of the preceding independently observed version.
  const overlapsPreviouslyObservedVersion =
    previousEnd != null && record.raw_end_epoch_s <= previousEnd;
  const start =
    previousEnd == null || overlapsPreviouslyObservedVersion
      ? record.raw_start_epoch_s
      : Math.max(record.raw_start_epoch_s, previousEnd);
  const end = record.raw_end_epoch_s;
  if (!Number.isFinite(start) || !Number.isFinite(end) || end <= start) {
    rows.push({
      version,
      directory: record.directory,
      available: false,
      reason: "insufficient_or_non_monotone_timestamp_evidence",
      raw_start_epoch_s: record.raw_start_epoch_s,
      raw_end_epoch_s: record.raw_end_epoch_s,
    });
    if (Number.isFinite(end))
      previousEnd = Math.max(previousEnd ?? end, end);
    continue;
  }

  rows.push({
    version,
    directory: record.directory,
    available: true,
    start_epoch_s: start,
    end_epoch_s: end,
    start_iso: new Date(start * 1000).toISOString(),
    end_iso: new Date(end * 1000).toISOString(),
    duration_minutes: (end - start) / 60,
    evidence_kind: "remote_artifact_mtime_window",
    file_count: record.file_count,
    raw_start_path: record.raw_start_path,
    raw_end_path: record.raw_end_path,
    start_was_clamped_to_previous_end:
      !overlapsPreviouslyObservedVersion &&
      previousEnd != null &&
      record.raw_start_epoch_s < previousEnd,
    overlaps_previously_observed_version: overlapsPreviouslyObservedVersion,
  });
  previousEnd = Math.max(previousEnd ?? end, end);
}

const available = rows.filter((row) => row.available);
const output = {
  generated_at: new Date().toISOString(),
  definition: {
    start:
      "Earliest retained artifact mtime in the version experiment directory after excluding source/workspace/dataset/copied-control paths and clamping inherited timestamps to the preceding observed version end.",
    end:
      "Latest retained artifact mtime in the version experiment directory.",
    duration:
      "Observed elapsed wall-clock minutes from start to end. This includes reasoning, implementation, compilation, targeted/full experiments, analysis, and documentation when those artifacts fall in the observed window.",
    limitation:
      "This is an artifact-backed lower-bound/observed work window, not active human or model compute time. Shared or single-point records are left missing.",
  },
  coverage: {
    versions: rows.length,
    available: available.length,
    missing: rows.length - available.length,
  },
  rows,
};

fs.writeFileSync(
  path.join(here, "version-time-data.json"),
  JSON.stringify(output, null, 2) + "\n"
);
console.log(JSON.stringify(output.coverage));
