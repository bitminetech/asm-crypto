#!/usr/bin/env python3
"""Ensure the real audit rejects an extra axiom and a mismatched proof type.

Deliberately invalid Lean fixtures are generated only in the ignored build
directory. They are not imported by any library or successful proof check.
"""
from pathlib import Path
import subprocess


def main():
    root = Path(__file__).resolve().parents[2]
    source = (root / "tests/runner/lean/CheckProofs.lean").read_text()
    output = root / "build/verification/negative"
    output.mkdir(parents=True, exist_ok=True)
    bad_axiom = source.replace(
        "open Lean Elab Command in",
        "axiom forbiddenAuditFixture : True\n"
        "theorem badAuditFixture : True := forbiddenAuditFixture\n\n"
        "open Lean Elab Command in")
    bad_axiom = bad_axiom.replace("let names := #[", "let names := #[``badAuditFixture,", 1)
    bad_statement = source.replace(
        "Crypto.Reference.sha256_matches_fips message h",
        "(fun (_ : False) => Crypto.Reference.sha256_matches_fips message h)", 1)
    for name, contents, expected in (
        ("ExtraAxiom", bad_axiom, "Forbidden axioms in badAuditFixture"),
        ("AddedAssumption", bad_statement, "Type mismatch"),
    ):
        path = output / (name + ".lean")
        path.write_text(contents)
        result = subprocess.run(["lake", "env", "lean", str(path)], cwd=root,
                                stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True)
        (output / (name + ".log")).write_text(result.stdout)
        if result.returncode == 0 or expected.lower() not in result.stdout.lower():
            raise RuntimeError(name + ": audit did not reject the intended violation\n" + result.stdout)
        print(name + ": correctly rejected")


if __name__ == "__main__":
    main()
