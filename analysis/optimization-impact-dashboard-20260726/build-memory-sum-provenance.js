#!/usr/bin/env node

const fs = require("fs");
const path = require("path");
const vm = require("vm");

const here = __dirname;
const input = process.argv[2];
if (!input || !fs.existsSync(input)) {
  throw new Error(
    "usage: build-memory-sum-provenance.js <remote-full-xml-summaries.jsonl>"
  );
}

const builder = fs.readFileSync(path.join(here, "build-dashboard-data.js"), "utf8");
const match = builder.match(/const exactOverrides = (\{[\s\S]*?\n\});/);
if (!match) throw new Error("cannot find exactOverrides");
const exact = vm.runInNewContext(`(${match[1]})`);
const summaries = fs
  .readFileSync(input, "utf8")
  .trim()
  .split("\n")
  .filter(Boolean)
  .map(JSON.parse);

const rows = [];
for (const [versionText, expected] of Object.entries(exact)) {
  const version = Number(versionText);
  const candidates = summaries
    .map((row) => ({
      ...row,
      distance:
        Math.abs(row.cpu - expected.cpu) +
        Math.abs(row.wall - expected.wall) +
        (row.correct === expected.correct ? 0 : 1e6),
    }))
    .sort((left, right) => left.distance - right.distance);
  const best = candidates[0];
  if (!best || best.distance >= 0.01) {
    throw new Error(`no exact XML match for V${version}`);
  }
  rows.push({
    version,
    correct: best.correct,
    cpu_s: best.cpu,
    wall_s: best.wall,
    memory_sum_b: best.memory_sum_b,
    source_xml: `/data3/sujie/experiments${best.path}`,
    tuple_distance: best.distance,
  });
}

fs.writeFileSync(
  path.join(here, "memory-sum-provenance.json"),
  JSON.stringify(
    {
      generated_at: new Date().toISOString(),
      definition:
        "Sum of the BenchExec memory column over exactly 725 run rows.",
      match_rule:
        "XML correct/CPU/wall tuple must match the registered exact725 point with total absolute CPU+wall error below 0.01 seconds.",
      rows,
    },
    null,
    2
  ) + "\n"
);
console.log(JSON.stringify({ matched_versions: rows.length }));
