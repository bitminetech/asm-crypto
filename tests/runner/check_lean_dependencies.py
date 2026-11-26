#!/usr/bin/env python3
"""Reject unpinned or modified imported Lean sources before checking proofs."""
import hashlib
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
    reference = json.loads((root / "lean/verification-scope.json").read_text())["reference"]
    if reference["commit"] != "784bccaf1632af158cbe8fd7c056137cfd6c47b8":
        raise ValueError("EthLib reference changed: review and register a new obligation")
    directory = root / "lean/Imports/ethlib"
    entries = list(directory.rglob("*"))
    if any(entry.is_symlink() for entry in [directory, *entries]):
        raise ValueError("symbolic links in the imported EthLib closure are not permitted")
    files = {entry.relative_to(directory).as_posix(): hashlib.sha256(entry.read_bytes()).hexdigest()
             for entry in entries if entry.is_file()}
    if files != reference["files_sha256"]:
        raise ValueError("imported EthLib SHA-256 source closure differs from the pin")
    report.append({"name": "EthLib", "commit": reference["commit"],
                   "url": reference["repository"], "path": reference["path"],
                   "files_sha256": files})
    model_path = "lean/Imports/arm64"
    model_pin = "b0f729accbc21a0413e7ca4e1da43fa45b5f2e1b"
    model = root / model_path
    if not (model / ".git").exists():
        raise ValueError("initialize the pinned ARM64 model: git submodule update --init")
    if git(root, "ls-files", "--stage", "--", model_path).split()[:2] != ["160000", model_pin]:
        raise ValueError("ARM64 model gitlink differs from configured upstream source pin")
    if git(model, "rev-parse", "HEAD") != model_pin or git(model, "status", "--porcelain", "--untracked-files=all"):
        raise ValueError("ARM64 model source revision changed or checkout was modified")
    report.append({"name": "arm64-model", "commit": model_pin,
                   "url": "https://github.com/google-deepmind/code-verification",
                   "path": model_path, "scope": "unchanged ISA/Syscalls source closure; no upstream proof tactics"})
    return report


if __name__ == "__main__":
    root = Path(__file__).resolve().parents[2]
    print(json.dumps(check(root), indent=2))
