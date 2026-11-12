#!/usr/bin/env python3
"""Reject unpinned or modified imported Lean sources before checking proofs."""
import json
from pathlib import Path
import re
import subprocess


def git(directory, *args):
    return subprocess.check_output(["git", "-C", str(directory), *args], text=True).strip()


def check(root):
    manifest = json.loads((root / "lake-manifest.json").read_text())
    report = []
    for package in manifest["packages"]:
        if package["type"] != "git" or not re.fullmatch("[0-9a-f]{40}", package["rev"]):
            raise ValueError("every imported dependency must have an exact Git pin")
        name = package["name"].strip("«»")
        directory = root / manifest["packagesDir"] / name
        if git(directory, "rev-parse", "HEAD") != package["rev"]:
            raise ValueError(name + ": dependency revision differs from pin")
        if git(directory, "status", "--porcelain", "--untracked-files=all"):
            raise ValueError(name + ": imported dependency was modified")
        report.append({"name": name, "commit": package["rev"], "url": package["url"]})
    reference = next(p for p in report if p["name"] == "fips-pub-180-4")
    if reference["commit"] != "0018b08f3458553ad511e92a96336979c1e0c45a":
        raise ValueError("reference changed: review and register a new obligation")
    return report


if __name__ == "__main__":
    root = Path(__file__).resolve().parents[2]
    print(json.dumps(check(root), indent=2))
