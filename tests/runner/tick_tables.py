"""
Write the tick table of every documented function into the Results section
of its document (ARCHITECTURE.md section 10).

Usage: python3 -I tests/runner/tick_tables.py RESULTS_DIR BUILD_DIR [ARM64_EQUAL_RECEIPT] [--x86-equal-receipt PATH]
Runs from the repo root.

- RESULTS_DIR holds results-<os>-<isa>.txt: the runner output of each target.
  Its "FUNCTION <name> PASS" lines give the functions whose vectors all passed.
- BUILD_DIR holds linux-<isa>/calls.txt from platform/check.py: the calls
  each function makes.

An OS cell gets a tick when that target's runner printed PASS for the
function. A function with no vectors of its own (an L0 helper) is tested
through the functions that call it: it gets a tick when every L2 or L3
function that reaches it passed on that target. A missing results file leaves the
cells of its target empty. The ARM64 and scalar x86-64 crypto_sha256 proof
cells each require a current checked receipt and passing vectors on all three
targets for that ISA. Missing or invalid receipts leave
proof cells empty.
"""

import argparse
import glob
import hashlib
import json
import os
import re
import sys
import subprocess
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
from prepare_arm64_equal_review import EXPECTED, source_digest

OSES = ("linux", "windows", "macos")
ISAS = (("x86_64", "x86-64"), ("arm64", "ARM64"), ("riscv64", "RISC-V"))
SUPPORTED = {(o, i) for o in OSES for i, _ in ISAS} - {("windows", "riscv64"), ("macos", "riscv64")}
TICK = "✅"
MARKER = "<!-- CI generates the tick table for each function here. -->"



ARM64_TARGETS = ["linux-arm64", "windows-arm64", "macos-arm64"]


def validate_equal_receipt(receipt_path, build_dir, root):
    """Bind the CI proof job's technical receipt to current sources/builds.

    Receipt authenticity comes from the successful proof job and its artifact;
    this consumer does not authenticate an arbitrary user-supplied JSON file.
    """
    root, build_dir = Path(root).resolve(), Path(build_dir).resolve()
    receipt = json.loads(Path(receipt_path).read_text())
    required = {"function": "crypto_sha256", "proof_id": "equal", "isa": "arm64",
                "theorem": "Crypto.ARM64.sha256.equal", "targets": ARM64_TARGETS,
                "supporting_checks": "passed", "kernel_replay": "fresh kernel; successful exit",
                "statement_comparison": "passed"}
    if not isinstance(receipt, dict) or any(receipt.get(k) != v for k, v in required.items()):
        raise ValueError("receipt does not identify the complete checked ARM64 SHA-256 claim")
    if type(receipt.get("schema")) is not int or receipt["schema"] != 1 or receipt.get("checked") is not True:
        raise ValueError("receipt is not checked schema 1")
    for key in ("expected_manifest_sha256", "expected_statement_sha256"):
        if not isinstance(receipt.get(key), str) or not re.fullmatch(r"[0-9a-f]{64}", receipt[key]):
            raise ValueError("receipt lacks a selected statement pin")
    if receipt["expected_statement_sha256"] != hashlib.sha256(EXPECTED.encode()).hexdigest():
        raise ValueError("receipt expected statement differs from the registered baseline")
    commit = subprocess.check_output(["git", "-C", str(root), "rev-parse", "HEAD"], text=True).strip()
    if receipt.get("git_commit") != commit:
        raise ValueError("receipt belongs to a different source commit")
    sources = receipt.get("source_sha256")
    if not isinstance(sources, dict) or "lean/Proofs/ARM64/NativeEqual.lean" not in sources:
        raise ValueError("receipt lacks the semantic source closure")
    for relative, digest in sources.items():
        if not isinstance(relative, str) or not isinstance(digest, str) or not re.fullmatch(r"[0-9a-f]{64}", digest):
            raise ValueError("invalid semantic source digest")
        path = (root / relative).resolve()
        if not path.is_relative_to(root) or source_digest(root, path) != digest:
            raise ValueError("receipt semantic dependency differs: " + relative)
    artifacts = receipt.get("artifacts")
    if not isinstance(artifacts, list) or len(artifacts) != 3 or any(not isinstance(a, dict) for a in artifacts):
        raise ValueError("receipt must bind three ARM64 artifacts")
    if sorted(a.get("target", "") for a in artifacts) != sorted(ARM64_TARGETS):
        raise ValueError("receipt ARM64 target set differs")
    image = bytes.fromhex((root / "lean/Models/arm64-sha256.text.hex").read_text())
    image_hash = hashlib.sha256(image).hexdigest()
    for artifact in artifacts:
        if (artifact.get("text_sha256") != image_hash or artifact.get("text_bytes") != 896 or
                len(image) != 896 or artifact.get("function_bytes") != 604 or artifact.get("entry_offset") != 0 or
                type(artifact.get("text_alignment_at_least")) is not int or artifact["text_alignment_at_least"] < 16 or
                artifact.get("object_unwind_checked") is not True or artifact.get("metadata_relocations_checked") is not True):
            raise ValueError("receipt lacks exact image/unwind evidence")
        directory = build_dir / artifact["target"]
        for filename, field in (("sha256.o", "object_sha256"), ("libasm-crypto.a", "archive_sha256")):
            if hashlib.sha256((directory / filename).read_bytes()).hexdigest() != artifact.get(field):
                raise ValueError("receipt artifact differs: " + artifact["target"] + "/" + filename)
    return True


def checked_equal(receipt_path, build_dir, root):
    if receipt_path is None:
        return False
    try:
        return validate_equal_receipt(receipt_path, build_dir, root)
    except (OSError, ValueError, TypeError, KeyError, subprocess.CalledProcessError) as error:
        print("ARM64 equal receipt ignored: " + str(error), file=sys.stderr)
        return False


def checked_x86_equal(receipt_path, build_dir, root):
    if receipt_path is None:
        return False
    try:
        from check_x86_64_equal_pin import EXPECTED as expected, TARGETS, THEOREM, check_artifacts, source_paths
        root = Path(root).resolve()
        receipt = json.loads(Path(receipt_path).read_text())
        fields = {"schema": 1, "function": "crypto_sha256", "proof_id": "equal", "isa": "x86_64",
                  "theorem": THEOREM, "targets": TARGETS, "supporting_checks": "passed",
                  "kernel_replay": "fresh kernel; successful exit", "statement_comparison": "passed"}
        if (not isinstance(receipt, dict) or any(receipt.get(k) != v for k, v in fields.items()) or
                type(receipt.get("schema")) is not int or receipt.get("checked") is not True):
            raise ValueError("receipt does not identify the complete checked x86-64 SHA-256 proof")
        if (not re.fullmatch("[0-9a-f]{64}", receipt.get("expected_manifest_sha256", "")) or
                receipt.get("expected_statement_sha256") != hashlib.sha256(expected.encode()).hexdigest()):
            raise ValueError("receipt lacks its selected x86-64 statement pin")
        commit = subprocess.check_output(["git", "-C", str(root), "rev-parse", "HEAD"], text=True).strip()
        if receipt.get("git_commit") != commit:
            raise ValueError("receipt belongs to a different source commit")
        sources = {str(path.relative_to(root)): source_digest(root, path) for path in source_paths(root)}
        if receipt.get("source_sha256") != sources:
            raise ValueError("receipt x86-64 semantic closure differs")
        if receipt.get("artifacts") != check_artifacts(Path(build_dir), root):
            raise ValueError("receipt x86-64 artifact identities differ")
        return True
    except (OSError, ValueError, TypeError, KeyError, subprocess.CalledProcessError) as error:
        print("x86-64 equal receipt ignored: " + str(error), file=sys.stderr)
        return False


def documented():
    """[(path, [(function, role)])] in document order."""
    docs = []
    for path in sorted(glob.glob("docs/reference/*.md")):
        functions, current = [], None
        with open(path, encoding="utf-8") as f:
            for line in f:
                m = re.match(r"## Function `([^`]+)`", line)
                if m:
                    current = [m.group(1), None]
                    functions.append(current)
                elif line.startswith("## "):
                    current = None
                elif current:
                    m = re.match(r"- Role: (L[012])\.", line)
                    if m:
                        current[1] = m.group(1)
        if functions:
            docs.append((path, [tuple(f) for f in functions]))
    return docs


def passed(results_dir, os_name, isa):
    path = os.path.join(results_dir, f"results-{os_name}-{isa}.txt")
    if not os.path.exists(path):
        return set()
    with open(path, encoding="utf-8", errors="replace") as f:
        text = f.read()
    # The file holds the output of the runner of each archive: a FAIL of either clears the tick.
    good = {m.group(1) for m in re.finditer(r"^FUNCTION (\S+) PASS\s*$", text, re.M)}
    return good - {m.group(1) for m in re.finditer(r"^FUNCTION (\S+) FAIL\s*$", text, re.M)}


def callers(build_dir, isa):
    """{callee: {callers}} from calls.txt."""
    graph = {}
    path = os.path.join(build_dir, f"linux-{isa}", "calls.txt")
    if os.path.exists(path):
        with open(path, encoding="utf-8") as f:
            for line in f:
                caller, callee = line.split()
                graph.setdefault(callee, set()).add(caller)
    return graph


def reaching_l2(function, graph, roles):
    """The L2 and L3 functions that call function, directly or through others."""
    seen, todo, found = set(), [function], set()
    while todo:
        for caller in graph.get(todo.pop(), ()):
            if caller in seen:
                continue
            seen.add(caller)
            if roles.get(caller) in ("L2", "L3"):
                found.add(caller)
            todo.append(caller)
    return found


def tick(function, role, os_name, isa, results_dir, graph, roles):
    if (os_name, isa) not in SUPPORTED:
        return False
    ok = passed(results_dir, os_name, isa)
    if function in ok:
        return True
    if role in ("L2", "L3"):
        return False
    tested_by = reaching_l2(function, graph, roles)
    return bool(tested_by) and tested_by <= ok


def table(function, role, results_dir, graphs, roles, equal_checked=False, x86_equal_checked=False):
    lines = [f"### `{function}`", "", "| ISA | Linux | Windows | macOS | `equal` |", "|---|---|---|---|---|"]
    for isa, label in ISAS:
        cells = [TICK if tick(function, role, o, isa, results_dir, graphs[isa], roles) else "" for o in OSES]
        checked = {"arm64": equal_checked, "x86_64": x86_equal_checked}.get(isa, False)
        proof = checked and function == "crypto_sha256" and all(cell == TICK for cell in cells)
        lines.append("| " + " | ".join([label] + cells + [TICK if proof else ""]) + " |")
    return "\n".join(lines)


def main(results_dir, build_dir, receipt_path=None, x86_receipt_path=None):
    root = Path(__file__).resolve().parents[2]
    equal_checked = checked_equal(receipt_path, build_dir, root)
    x86_equal_checked = checked_x86_equal(x86_receipt_path, build_dir, root)
    docs = documented()
    roles = {f: r for _, functions in docs for f, r in functions}
    graphs = {isa: callers(build_dir, isa) for isa, _ in ISAS}
    for path, functions in docs:
        with open(path, encoding="utf-8") as f:
            text = f.read()
        m = re.search(r"^## Results\n", text, re.M)
        if not m:
            sys.exit(f"{path}: no Results section")
        end = re.search(r"^## ", text[m.end():], re.M)
        rest = text[m.end() + end.start():] if end else ""
        tables = "\n\n".join(table(f, r, results_dir, graphs, roles, equal_checked, x86_equal_checked)
                             for f, r in functions)
        new = text[: m.end()] + "\n" + MARKER + "\n\n" + tables + "\n" + ("\n" + rest if rest else "")
        if new != text:
            with open(path, "w", encoding="utf-8") as f:
                f.write(new)
            print(f"updated {path}")


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("results_dir")
    parser.add_argument("build_dir")
    parser.add_argument("arm64_receipt", nargs="?")
    parser.add_argument("--x86-equal-receipt")
    args = parser.parse_args()
    main(args.results_dir, args.build_dir, args.arm64_receipt, args.x86_equal_receipt)
