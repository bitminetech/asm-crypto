#!/usr/bin/env python3
"""Prepare and check the externally pinned HMAC-SHA-256 Linux statements."""
import argparse
import hashlib
import json
from pathlib import Path
import re
import subprocess
import sys

sys.path.insert(0, str(Path(__file__).resolve().parent))
from check_hmac_linked_images import check as check_artifacts
from prepare_arm64_equal_review import source_digest as shared_digest, source_paths as shared_paths

ROOT = Path(__file__).resolve().parents[2]
RECEIPT = "checked-equal-hmac-sha256.json"
SUPPORT = "hmac-sha256-status.json"
TARGETS = {
    "linux-arm64": ("ARM64", "AAPCS64"),
    "linux-x86_64": ("X86_64", "System V AMD64"),
    "linux-riscv64": ("RISCV64", "RV64GC LP64D"),
}
FUNCTIONS = ("crypto_hmac_sha256", "crypto_hmac_key", "crypto_hmac_finish")
CLAIMS = {
    target: {
        "profile": profile,
        "theorems": {function: f"Crypto.HMACSHA256.{isa}.{function.removeprefix('crypto_')}.equal"
                     for function in FUNCTIONS},
    }
    for target, (isa, profile) in TARGETS.items()
}
THEOREMS = tuple(theorem for claim in CLAIMS.values() for theorem in claim["theorems"].values())
PROOF_CHECKS = {"supporting_checks": "passed", "kernel_replay": "fresh kernel; successful exit"}
HMAC_DOC = "docs/reference/hmac.md"


def expected_statement():
    examples = []
    for theorem in THEOREMS:
        requirements = theorem.removesuffix(".equal") + ".requirements"
        examples.append(f"example : Crypto.Baseline.Stateless.Equal {requirements} :=\n  {theorem}\n")
    return "import Proofs.HMACSHA256\n\n" + "\n".join(examples)


def sha256(data):
    return hashlib.sha256(data).hexdigest()


def commit(root):
    return subprocess.check_output(["git", "-C", root, "rev-parse", "HEAD"], text=True).strip()


def source_digest(root, path):
    if path.relative_to(root).as_posix() != HMAC_DOC:
        return shared_digest(root, path)
    text = path.read_text(encoding="utf-8")
    results = re.search(r"^## Results\n(.*?)(?=^## |\Z)", text, re.M | re.S)
    if results is None:
        raise ValueError("HMAC requirements need a generated Results section")
    rows = "\n".join(rf"\| {isa} \| (?:✅)? \| (?:✅)? \| (?:✅)? \| (?:✅)? \|"
                     for isa in ("x86-64", "ARM64", "RISC-V"))
    header = re.escape("| ISA | Linux | Windows | macOS | `equal` |\n|---|---|---|---|---|")
    def table(function):
        return re.escape(f"### `{function}`\n\n") + header + "\n" + rows

    expected = re.escape("<!-- CI generates the tick table for each function here. -->\n\n")
    expected += "\n\n".join(map(table, FUNCTIONS))
    if not re.fullmatch(expected, results.group(1).strip()):
        raise ValueError("unrecognized HMAC Results content")
    normalized = text[:results.start(1)] + "\n<!-- generated Results tables -->\n\n" + text[results.end(1):]
    return sha256(normalized.encode())


def source_hashes(root):
    paths = set(shared_paths(root)) | {root / HMAC_DOC}
    for isa in ("x86_64", "riscv64"):
        paths.update((root / f"asm/core/{isa}").rglob("*.s"))
    if any(path.is_symlink() or not path.is_file() or not path.resolve().is_relative_to(root) for path in paths):
        raise ValueError("proof sources must be regular files inside the checkout")
    return {path.relative_to(root).as_posix(): source_digest(root, path) for path in sorted(paths)}


def raw_json(value):
    return (json.dumps(value, sort_keys=True, separators=(",", ":")) + "\n").encode()


def manifest(root):
    gitlink = subprocess.check_output(["git", "-C", root, "ls-tree", "HEAD", "lean/Imports/arm64"], text=True).split()
    if len(gitlink) != 4 or gitlink[:2] != ["160000", "commit"]:
        raise ValueError("missing pinned ARM64 ISA model")
    scope = json.loads((root / "lean/verification-scope.json").read_text())
    return {
        "schema": 1, "proof_id": "equal", "claims": CLAIMS,
        "expected_statement": expected_statement(),
        "source_closure_sha256": sha256(raw_json(source_hashes(root))),
        "arm64_isa_commit": gitlink[2],
        "lean_dependencies": json.loads((root / "lake-manifest.json").read_text()),
        "standard_commit": scope["standard"]["commit"],
    }


def validate_manifest(root, raw, expected_sha256):
    if not re.fullmatch(r"[a-f0-9]{64}", expected_sha256) or sha256(raw) != expected_sha256:
        raise ValueError("external HMAC-SHA-256 manifest digest differs")
    selected = json.loads(raw)
    if selected != manifest(root):
        raise ValueError("external HMAC-SHA-256 statements or semantic source closure differ")
    return selected


def evidence(root, build, output):
    audit = (output / "hmac-sha256-axioms.log").read_text().splitlines()
    passed = [line.split("AXIOMS PASS ", 1)[1].split(":", 1)[0] for line in audit if "AXIOMS PASS " in line]
    if set(passed) != set(THEOREMS):
        raise ValueError("HMAC-SHA-256 axiom audit differs from the nine registered theorems")
    return {
        **PROOF_CHECKS, "git_commit": commit(root),
        "source_closure_sha256": sha256(raw_json(source_hashes(root))),
        "axiom_audit": passed, "artifacts": check_artifacts(build, "llvm-nm", root),
    }


def receipt_fields(root, build, selected_hash):
    return {
        **PROOF_CHECKS, "schema": 1, "proof_id": "equal", "checked": True, "claims": CLAIMS,
        "git_commit": commit(root), "source_closure_sha256": sha256(raw_json(source_hashes(root))),
        "expected_manifest_sha256": selected_hash,
        "expected_statement_sha256": sha256(expected_statement().encode()),
        "artifacts": check_artifacts(build, "llvm-nm", root),
    }


def checked_receipt(root, build, selected, selected_hash, support):
    result = receipt_fields(root, build, selected_hash)
    if type(support) is not dict or set(support.get("axiom_audit", [])) != set(THEOREMS):
        raise ValueError("HMAC-SHA-256 proof evidence is missing a theorem audit")
    for key in (*PROOF_CHECKS, "git_commit", "source_closure_sha256", "artifacts"):
        if support.get(key) != result[key]:
            raise ValueError(f"HMAC-SHA-256 proof evidence differs: {key}")
    if selected["source_closure_sha256"] != result["source_closure_sha256"]:
        raise ValueError("HMAC-SHA-256 pin and receipt cover different sources")
    return result


def validate_receipt(root, build, result):
    if type(result) is not dict or type(result.get("schema")) is not int or result.get("checked") is not True:
        raise ValueError("invalid HMAC-SHA-256 proof receipt")
    pin = result.get("expected_manifest_sha256")
    if not isinstance(pin, str) or re.fullmatch(r"[a-f0-9]{64}", pin) is None:
        raise ValueError("HMAC-SHA-256 proof receipt lacks the external pin")
    if result != receipt_fields(root, build, pin):
        raise ValueError("HMAC-SHA-256 proof receipt does not match this build")
    return {target: set(claim["theorems"]) for target, claim in CLAIMS.items()}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("action", choices=("prepare", "report", "check", "verify"))
    parser.add_argument("--trusted-manifest", type=Path)
    parser.add_argument("--trusted-sha256")
    for name in ("candidate", "evidence", "build", "output"):
        parser.add_argument("--" + name, type=Path)
    args = parser.parse_args()
    if args.action == "verify":
        if not all((args.candidate, args.evidence, args.build, args.output, args.trusted_manifest, args.trusted_sha256)):
            parser.error("verify requires the candidate, external pin, CI evidence, build and receipt output")
        root = args.candidate.resolve()
        selected = validate_manifest(root, args.trusted_manifest.read_bytes(), args.trusted_sha256)
        support = json.loads((args.evidence / SUPPORT).read_text())
        result = checked_receipt(root, args.build, selected, args.trusted_sha256, support)
        if result != json.loads((args.evidence / RECEIPT).read_text()):
            raise ValueError("HMAC-SHA-256 receipt differs from the trusted validation")
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_bytes(raw_json(result))
        return

    build = ROOT / "build"
    output = build / "verification"
    output.mkdir(parents=True, exist_ok=True)
    if args.action == "prepare":
        review = output / "hmac-equal-review"
        review.mkdir(exist_ok=True)
        data = raw_json(manifest(ROOT))
        (review / "manifest.json").write_bytes(data)
        (review / "Expected.lean").write_text(expected_statement())
        print("Candidate manifest SHA-256: " + sha256(data))
    elif args.action == "report":
        (output / SUPPORT).write_bytes(raw_json(evidence(ROOT, build, output)))
    else:
        receipt = output / RECEIPT
        receipt.unlink(missing_ok=True)
        if args.trusted_manifest is None or args.trusted_manifest.resolve().is_relative_to(ROOT):
            parser.error("the selected HMAC manifest must be supplied outside the candidate checkout")
        if not args.trusted_sha256:
            parser.error("the selected HMAC manifest digest is required")
        selected = validate_manifest(ROOT, args.trusted_manifest.read_bytes(), args.trusted_sha256)
        expected = output / "ExternallyPinnedExpectedHmac.lean"
        expected.write_text(selected["expected_statement"])
        subprocess.run(["lake", "env", "lean", expected], cwd=ROOT, check=True)
        support = json.loads((output / SUPPORT).read_text())
        receipt.write_bytes(raw_json(checked_receipt(ROOT, build, selected, args.trusted_sha256, support)))


if __name__ == "__main__":
    main()
