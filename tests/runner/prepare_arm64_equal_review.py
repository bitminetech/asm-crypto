#!/usr/bin/env python3
"""Generate the ARM64 expected-statement and source-hash manifest.

The manifest covers local Lean sources, validation tools and build inputs.
CI compares it with the technical pin selected outside the implementation repo.
"""
import hashlib
import json
from pathlib import Path
import re


EXPECTED = """import Proofs

example : Crypto.Baseline.Stateless.Equal Crypto.ARM64.NativeRequirements.requirements :=
  Crypto.ARM64.sha256.equal
"""


HEATMAP_START = "<!-- CI generates the verification heatmap here. -->"
HEATMAP_END = "<!-- End of the verification heatmap. -->"


def heatmap_picture(name, alt, title=None):
    """The exact picture element that tests/runner/heatmap.py writes."""
    extra = ' title="' + title + '"' if title is not None else ""
    return (r'<picture><source media="\(prefers-color-scheme: dark\)" srcset="docs/heatmap/' +
            name + r'-dark\.svg"><img src="docs/heatmap/' + name + r'-light\.svg" alt="' +
            alt + '"' + extra + r'></picture>')


def heatmap_pattern():
    section, function = r"[a-z0-9-]+", r"[A-Za-z0-9_]+"
    level = r"(?:Not proved|Proved on 1 ISA|2 ISAs|All 3 ISAs)"
    label = ("(?:" + heatmap_picture("label-" + section, section) + "|" +
             heatmap_picture("label", "") + ")")
    cell = ('<a href="docs/reference/' + section + r'\.md#function-' + function + '">' +
            heatmap_picture("cell-[0-3]", function, function + ": " + level) + "</a>")
    row = label + "(?:" + cell + ")+"
    body = (r"<table><tr><td>\n\n" +
            heatmap_picture("header", r"asm-crypto formal verification: [0-9]+ of [0-9]+ functions proved") +
            r"\n\n" + row + r"(?:<br>\n" + row + r")*\n\n" + heatmap_picture("legend", "Legend") +
            r"\n\n</td></tr></table>\n")
    return re.compile("(?:" + body + ")?")


def source_digest(root, path):
    """Pin requirements while excluding only strictly recognized CI tables."""
    data = path.read_bytes()
    if path.relative_to(root).as_posix() == "README.md":
        text = data.decode("utf-8")
        if text.count(HEATMAP_START) > 1 or text.count(HEATMAP_END) > 1:
            raise ValueError("README must have at most one generated heatmap")
        start, end = text.find(HEATMAP_START), text.find(HEATMAP_END)
        if start >= 0 or end >= 0:
            if start < 0 or end < start:
                raise ValueError("README heatmap markers are out of order")
            body = text[start + len(HEATMAP_START) + 1:end]
            if text[start + len(HEATMAP_START)] != "\n" or heatmap_pattern().fullmatch(body) is None:
                raise ValueError("unrecognized generated heatmap content; refusing to omit it from the pin")
            text = (text[:start] + "<!-- generated verification heatmap -->" +
                    text[end + len(HEATMAP_END):])
            data = text.encode("utf-8")
    if path.relative_to(root).as_posix() == "docs/reference/sha-256.md":
        text = data.decode("utf-8")
        match = re.search(r"^## Results\n(.*?)(?=^## |\Z)", text, re.M | re.S)
        if match is None:
            raise ValueError("SHA-256 requirements must have one generated Results section")
        body = match.group(1).strip()
        placeholder = "<!-- CI generates the tick table here. -->"
        marker = "<!-- CI generates the tick table for each function here. -->"
        generated = (re.escape(marker) + r"\n\n### `crypto_sha256`\n\n" +
                     re.escape("| ISA | Linux | Windows | macOS | `equal` |") + r"\n" +
                     re.escape("|---|---|---|---|---|") + r"\n" +
                     r"\| x86-64 \| (?:✅)? \| (?:✅)? \| (?:✅)? \| (?:✅)? \|\n" +
                     r"\| ARM64 \| (?:✅)? \| (?:✅)? \| (?:✅)? \| (?:✅)? \|\n" +
                     r"\| RISC-V \| (?:✅)? \| (?:✅)? \| (?:✅)? \| (?:✅)? \|")
        if body != placeholder and re.fullmatch(generated, body) is None:
            raise ValueError("unrecognized generated Results content; refusing to omit it from the pin")
        text = text[:match.start(1)] + "\n<!-- generated Results table -->\n\n" + text[match.end(1):]
        data = text.encode("utf-8")
    return hashlib.sha256(data).hexdigest()


def source_paths(root):
    for directory in ("tests", "platform", ".github"):
        if any(p.is_symlink() for p in (root / directory).rglob("*")):
            raise ValueError("source symlinks are not admitted in " + directory)
    return sorted(
        [p for p in (root / "lean").rglob("*.lean")
         if "Imports" not in p.relative_to(root / "lean").parts]
        + list((root / "include").rglob("*.inc"))
        + list((root / "asm/core/arm64").rglob("*.s"))
        + [p for p in (root / "tests/runner").rglob("*.py") if "__pycache__" not in p.parts]
        + list((root / "tests/runner").glob("*.sh"))
        + list((root / "tests/runner/lean").glob("*.lean"))
        + list((root / "tests/runner").glob("*.c"))
        + [p for p in (root / "tests/generator").rglob("*")
           if p.is_file() and "__pycache__" not in p.parts]
        + list((root / ".github/workflows").glob("*.yml"))
        + list((root / ".github/workflows").glob("*.yaml"))
        + list((root / "docs/models").glob("*.md"))
        + [p for p in (root / "platform").rglob("*")
           if p.is_file() and "__pycache__" not in p.parts and p.suffix not in (".pyc", ".pyo")]
        + [root / name for name in (
            "lakefile.toml", "lake-manifest.json", "lean-toolchain", ".gitmodules",
            "lean/Models/arm64-sha256.text.hex", "lean/verification-scope.json",
            "docs/reference/sha-256.md", "README.md")])


def main():
    root = Path(__file__).resolve().parents[2]
    output = root / "build/verification/arm64-equal-review"
    output.mkdir(parents=True, exist_ok=True)
    (output / "Expected.lean").write_text(EXPECTED)
    manifest = {
        "schema": 1,
        "claim": "ARM64 crypto_sha256 equal technical baseline",
        "theorem": "Crypto.ARM64.sha256.equal",
        "expected_statement": EXPECTED,
        "source_sha256": {
            str(p.relative_to(root)): source_digest(root, p)
            for p in source_paths(root)},
        "external_dependencies": json.loads((root / "lake-manifest.json").read_text()),
        "isa_model_commit": "b0f729accbc21a0413e7ca4e1da43fa45b5f2e1b",
        "standard_commit": json.loads((root / "lean/verification-scope.json").read_text())["standard"]["commit"],
        "policy": "The external technical pin fixes the expected statement and source closure. CI checks that pin alongside kernel replay, axiom auditing and exact artifact validation."
    }
    data = (json.dumps(manifest, indent=2, sort_keys=True) + "\n").encode()
    (output / "manifest.json").write_bytes(data)
    print("Technical baseline manifest SHA-256: " + hashlib.sha256(data).hexdigest())


if __name__ == "__main__":
    main()
