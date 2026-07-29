#!/usr/bin/env python3

import bz2
import json
import sys
import xml.etree.ElementTree as ET
from pathlib import Path


def load(path):
    root = ET.fromstring(bz2.open(path, "rb").read())
    runs = {}
    for run in root.findall("run"):
        columns = {
            column.get("title"): column.get("value")
            for column in run.findall("column")
        }
        name = Path(run.get("name")).name
        runs[name] = {
            "status": columns["status"],
            "category": columns["category"],
            "cpu": float(columns["cputime"].removesuffix("s")),
            "wall": float(columns["walltime"].removesuffix("s")),
            "memory": int(columns["memory"].removesuffix("B")),
        }
    return root, runs


def summary(runs):
    return {
        "correct": sum(run["category"] == "correct" for run in runs.values()),
        "wrong": sum(run["category"] == "wrong" for run in runs.values()),
        "unfinished": sum(
            run["category"] not in {"correct", "wrong"}
            for run in runs.values()
        ),
        "cpu": sum(run["cpu"] for run in runs.values()),
        "wall": sum(run["wall"] for run in runs.values()),
        "memory": sum(run["memory"] for run in runs.values()),
        "peak_memory": max(run["memory"] for run in runs.values()),
    }


def main():
    if len(sys.argv) != 3:
        raise SystemExit("usage: analyze_exact.py BASE.xml.bz2 CANDIDATE.xml.bz2")
    base_root, base = load(sys.argv[1])
    candidate_root, candidate = load(sys.argv[2])
    if set(base) != set(candidate):
        raise SystemExit("task sets differ")
    base_summary = summary(base)
    candidate_summary = summary(candidate)
    changes = []
    for name in sorted(base):
        before = base[name]
        after = candidate[name]
        if (before["status"], before["category"]) != (
            after["status"],
            after["category"],
        ):
            changes.append(
                {
                    "task": name,
                    "before_status": before["status"],
                    "before_category": before["category"],
                    "after_status": after["status"],
                    "after_category": after["category"],
                }
            )
    result = {
        "base": {
            "start": base_root.get("starttime"),
            "end": base_root.get("endtime"),
            **base_summary,
        },
        "candidate": {
            "start": candidate_root.get("starttime"),
            "end": candidate_root.get("endtime"),
            **candidate_summary,
        },
        "percent_change": {
            key: 100.0 * (candidate_summary[key] / base_summary[key] - 1.0)
            for key in ("cpu", "wall", "memory")
        },
        "old_correct_losses": [
            name
            for name in sorted(base)
            if base[name]["category"] == "correct"
            and candidate[name]["category"] != "correct"
        ],
        "new_wrong": [
            name
            for name in sorted(base)
            if base[name]["category"] != "wrong"
            and candidate[name]["category"] == "wrong"
        ],
        "changes": changes,
    }
    print(json.dumps(result, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
