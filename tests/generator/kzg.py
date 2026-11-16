"""
Write the vector files for KZG: the blob functions, the cell functions and
the trusted setup.

Usage: python3 -I kzg.py OUT_DIR

Sources:
- Official cases: tests/cryptography/kzg of ethereum/cryptography-specs at
  the pinned commit, which run.sh fetches into OUT_DIR/sources/cryptography-specs.
  Each file is checked against the pinned SHA256SUMS, and SHA256SUMS against
  its pinned SHA-256. The expected outputs are those of the cases.
- The trusted setup of every case: EthLib/Cryptography/Kzg/TrustedSetupData.lean
  at the same commit, checked against its pinned SHA-256.
- A case gives no output when the spec rejects its input. The status the
  function must return then follows the order of the checks of the spec
  (Core.lean, Cells.lean, Recovery.lean, Exports/Kzg.lean), written out here;
  the point checks use the key check of bls.py (py_arkworks_bls12381). The
  script stops when these checks and a case disagree on whether it fails.
- Generated cases: TrustedSetup.ofBytes on setups with a list of the wrong
  length or a point that does not decompress.
The file format is in README.md.
"""

import hashlib
import importlib.util
import os
import re
import struct
import sys

import yaml

COMMIT = "bb6dfe55198243682bc2eaf94611af2dbce1be6f"   # ethereum/cryptography-specs v0.3.0, fetched by run.sh
KZG_SUMS = "11341d6864faaeec2302c12b1ac5bb215c7757b5fbd6e6e2eb69ff496b19bc71"
SETUP_SHA = "ea834a0ed4af25acb32e47a9852a445fd0522b5943bdcbdb8bde8f3fea67b7a5"

# include/crypto.inc and include/kzg.inc
OK, INVALID_ENCODING = 0, 10
INVALID_COMMITMENT, INVALID_PROOF, LENGTH_MISMATCH, CELL_INDEX, COMMITMENT_INDEX = 13, 14, 15, 16, 17
NOT_ASCENDING, NOT_ENOUGH_CELLS, TOO_MANY_CELLS, INVALID_TRUSTED_SETUP = 18, 19, 20, 21
# tests/generator/README.md, primitive file kinds
(K_SETUP, K_COMMIT, K_PROOF, K_VERIFY, K_BLOB_PROOF, K_BLOB_VERIFY, K_BLOB_BATCH, K_CHALLENGE,
 K_CELLS, K_CELLS_PROOFS, K_CELL_BATCH, K_RECOVER, K_CELL_CHALLENGE) = range(36, 49)

R = 0x73eda753299d7d483339d80809a1d80553bda402fffe5bfeffffffff00000001
G1_INF = b"\xc0" + bytes(47)
BLOB, CELL, CELLS = 131072, 2048, 128

out_dir = sys.argv[1]
specs = os.path.join(out_dir, "sources", "cryptography-specs")
here = os.path.dirname(os.path.abspath(__file__))
spec = importlib.util.spec_from_file_location("bls", os.path.join(here, "bls.py"))
bls = importlib.util.module_from_spec(spec)
spec.loader.exec_module(bls)           # its main part runs only as a script


def pinned(path, digest):
    data = open(os.path.join(specs, path), "rb").read()
    if hashlib.sha256(data).hexdigest() != digest:
        raise SystemExit(f"kzg.py: {path}: SHA-256 does not match its pin")
    return data


def official():
    """(handler, case, parsed data.yaml) for every case, in the order of SHA256SUMS."""
    sums = pinned("tests/cryptography/kzg/SHA256SUMS", KZG_SUMS).decode()
    for line in sums.splitlines():
        if not line or line.startswith("#"):
            continue
        digest, path = line.split()
        handler, case = path.split("/")[:2]
        yield handler, case, yaml.safe_load(pinned(f"tests/cryptography/kzg/{path}", digest))


def setup_lists():
    """The three lists of TrustedSetupData.lean, as lists of point bytes."""
    text = pinned("EthLib/Cryptography/Kzg/TrustedSetupData.lean", SETUP_SHA).decode()
    lists = []
    for name in ("g1LagrangeHex", "g1MonomialHex", "g2MonomialHex"):
        body = text.split(f"def {name} : Array String := #[", 1)[1].split("]", 1)[0]
        lists.append([bytes.fromhex(h) for h in re.findall(r'"([0-9a-fA-F]+)"', body)])
    if [len(x) for x in lists] != [4096, 4096, 65]:
        raise SystemExit("kzg.py: TrustedSetupData.lean: unexpected list lengths")
    return lists


def hx(s):
    s = str(s)
    return bytes.fromhex(s[2:] if s.startswith("0x") else s)


def cell(v):
    """A cell: one hex string, or a list of its 64 field elements (cosets_evals)."""
    return b"".join(hx(e) for e in v) if isinstance(v, list) else hx(v)


# ---------------------------------------------------------------- the checks of the spec

def field_ok(b):
    """bytesToBlsField."""
    return int.from_bytes(b, "big") < R


def blob_ok(b):
    """blobToPolynomial."""
    return all(field_ok(b[i:i + 32]) for i in range(0, len(b), 32))


def g1_ok(b):
    """validateKzgG1Point: the point at infinity in its one form, or KeyValidate."""
    return b == G1_INF or bls.key_validate(b) is not None


def first_failure(checks):
    """The status of the first check that fails, in order, else OK."""
    for ok, status in checks:
        if not ok():
            return status
    return OK


def st_verify(commitment, z, y, proof):
    return first_failure([(lambda: g1_ok(commitment), INVALID_COMMITMENT), (lambda: g1_ok(proof), INVALID_PROOF),
                          (lambda: field_ok(z), INVALID_ENCODING), (lambda: field_ok(y), INVALID_ENCODING)])


def st_blob_batch(blobs, commitments, proofs):
    if len(commitments) != len(blobs) or len(proofs) != len(blobs):
        return LENGTH_MISMATCH
    for b, c, p in zip(blobs, commitments, proofs):
        st = first_failure([(lambda: g1_ok(c), INVALID_COMMITMENT), (lambda: blob_ok(b), INVALID_ENCODING),
                            (lambda: g1_ok(p), INVALID_PROOF)])
        if st != OK:
            return st
    return OK


def st_cell_batch(commitments, indices, cells, proofs):
    n = len(commitments)
    if len(cells) != n or len(proofs) != n or len(indices) != n:
        return LENGTH_MISMATCH
    if any(i >= CELLS for i in indices):
        return CELL_INDEX
    if not all(g1_ok(c) for c in commitments):
        return INVALID_COMMITMENT
    if not all(blob_ok(c) for c in cells):
        return INVALID_ENCODING
    if not all(g1_ok(p) for p in proofs):
        return INVALID_PROOF
    return OK


def st_recover(indices, cells):
    if len(cells) != len(indices):
        return LENGTH_MISMATCH
    if len(indices) < CELLS // 2:
        return NOT_ENOUGH_CELLS
    if len(indices) > CELLS:
        return TOO_MANY_CELLS
    if any(i >= CELLS for i in indices):
        return CELL_INDEX
    if any(b <= a for a, b in zip(indices, indices[1:])):
        return NOT_ASCENDING
    if not all(blob_ok(c) for c in cells):
        return INVALID_ENCODING
    return OK


def st_cell_challenge(commitments, commitment_indices, indices, cells, proofs):
    n = len(commitment_indices)
    if len(indices) != n or len(cells) != n or len(proofs) != n:
        return LENGTH_MISMATCH
    if not all(g1_ok(c) for c in commitments):
        return INVALID_COMMITMENT
    if any(i >= len(commitments) for i in commitment_indices):
        return COMMITMENT_INDEX
    if any(i >= CELLS for i in indices):
        return CELL_INDEX
    if not all(g1_ok(p) for p in proofs):
        return INVALID_PROOF
    if not all(blob_ok(c) for c in cells):
        return INVALID_ENCODING
    return OK


# ---------------------------------------------------------------- case files

def u64(n):
    return struct.pack("<Q", n)


def blob(b):
    return u64(len(b)) + b


def u64s(xs):
    return blob(b"".join(u64(x) for x in xs))


manifest = []


class CaseFile:
    def __init__(self, name):
        self.name, self.cases = name, []

    def add(self, kind, case, *fields):
        self.cases.append(u64(kind) + blob(case.encode()) + b"".join(fields))

    def write(self):
        data = b"CRYPTOV2" + u64(len(self.cases)) + b"".join(self.cases)
        with open(os.path.join(out_dir, self.name), "wb") as f:
            f.write(data)
        manifest.append(f"{self.name} {len(self.cases)} {hashlib.sha256(data).hexdigest()}")
        print(f"{self.name}: {len(self.cases)} cases")


def agree(case, status, output):
    """The case has an output exactly when the checks pass."""
    if (status == OK) != (output is not None):
        raise SystemExit(f"kzg.py: {case}: the checks give status {status}, the case output {output!r:.40}")


def result(status, data, size):
    return u64(status) + (data if status == OK else bytes(size))


def add_setup(f, case, lists, status):
    f.add(K_SETUP, case, *(blob(b"".join(x)) for x in lists), u64(status))


# ---------------------------------------------------------------- official cases

def sizes_ok(handler, i):
    """True when every value of a case has its fixed size."""
    fixed = {"blob": BLOB, "commitment": 48, "proof": 48, "z": 32, "y": 32}
    for key, n in fixed.items():
        if key in i and len(hx(i[key])) != n:
            return False
    lists = {"blobs": BLOB, "commitments": 48, "proofs": 48}
    for key, n in lists.items():
        if key in i and any(len(hx(v)) != n for v in i[key]):
            return False
    for key in ("cells", "cosets_evals"):
        if key in i and any(len(cell(v)) != CELL or (isinstance(v, list) and any(len(hx(e)) != 32 for e in v))
                            for v in i[key]):
            return False
    for key in ("cell_indices", "commitment_indices"):
        if key in i and any(not 0 <= v < 2 ** 64 for v in i[key]):
            return False
    return True


def write_official(lists):
    f = CaseFile("kzg-official.bin")
    add_setup(f, "trusted_setup", lists, OK)
    for handler, case, d in official():
        i, o = d["input"], d["output"]
        if not sizes_ok(handler, i):
            print(f"left out: {handler}/{case}, a value of another size")
            continue
        if handler == "blob_to_kzg_commitment":
            b = hx(i["blob"])
            st = OK if blob_ok(b) else INVALID_ENCODING
            agree(case, st, o)
            f.add(K_COMMIT, case, b, result(st, o and hx(o), 48))
        elif handler == "compute_kzg_proof":
            b, z = hx(i["blob"]), hx(i["z"])
            st = first_failure([(lambda: blob_ok(b), INVALID_ENCODING), (lambda: field_ok(z), INVALID_ENCODING)])
            agree(case, st, o)
            f.add(K_PROOF, case, b, z, result(st, o and hx(o[0]) + hx(o[1]), 80))
        elif handler == "verify_kzg_proof":
            c, z, y, p = (hx(i[k]) for k in ("commitment", "z", "y", "proof"))
            st = st_verify(c, z, y, p)
            agree(case, st, o)
            f.add(K_VERIFY, case, c, z, y, p, u64(st), u64(int(bool(o))))
        elif handler == "compute_blob_kzg_proof":
            b, c = hx(i["blob"]), hx(i["commitment"])
            st = first_failure([(lambda: g1_ok(c), INVALID_COMMITMENT), (lambda: blob_ok(b), INVALID_ENCODING)])
            agree(case, st, o)
            f.add(K_BLOB_PROOF, case, b, c, result(st, o and hx(o), 48))
        elif handler == "verify_blob_kzg_proof":
            b, c, p = hx(i["blob"]), hx(i["commitment"]), hx(i["proof"])
            st = first_failure([(lambda: g1_ok(c), INVALID_COMMITMENT), (lambda: blob_ok(b), INVALID_ENCODING),
                                (lambda: g1_ok(p), INVALID_PROOF)])
            agree(case, st, o)
            f.add(K_BLOB_VERIFY, case, b, c, p, u64(st), u64(int(bool(o))))
        elif handler == "verify_blob_kzg_proof_batch":
            bs, cs, ps = ([hx(v) for v in i[k]] for k in ("blobs", "commitments", "proofs"))
            st = st_blob_batch(bs, cs, ps)
            agree(case, st, o)
            f.add(K_BLOB_BATCH, case, blob(b"".join(bs)), blob(b"".join(cs)), blob(b"".join(ps)),
                  u64(st), u64(int(bool(o))))
        elif handler == "compute_challenge":
            b, c = hx(i["blob"]), hx(i["commitment"])
            st = first_failure([(lambda: blob_ok(b), INVALID_ENCODING), (lambda: g1_ok(c), INVALID_COMMITMENT)])
            agree(case, st, o)
            f.add(K_CHALLENGE, case, b, c, result(st, o and hx(o), 32))
        elif handler == "compute_cells":
            b = hx(i["blob"])
            st = OK if blob_ok(b) else INVALID_ENCODING
            agree(case, st, o)
            f.add(K_CELLS, case, b, result(st, o and b"".join(hx(v) for v in o), CELLS * CELL))
        elif handler == "compute_cells_and_kzg_proofs":
            b = hx(i["blob"])
            st = OK if blob_ok(b) else INVALID_ENCODING
            agree(case, st, o)
            out = o and b"".join(hx(v) for v in o[0]) + b"".join(hx(v) for v in o[1])
            f.add(K_CELLS_PROOFS, case, b, result(st, out, CELLS * CELL + CELLS * 48))
        elif handler == "verify_cell_kzg_proof_batch":
            cs, ps = ([hx(v) for v in i[k]] for k in ("commitments", "proofs"))
            cells, idx = [cell(v) for v in i["cells"]], i["cell_indices"]
            st = st_cell_batch(cs, idx, cells, ps)
            agree(case, st, o)
            f.add(K_CELL_BATCH, case, blob(b"".join(cs)), u64s(idx), blob(b"".join(cells)), blob(b"".join(ps)),
                  u64(st), u64(int(bool(o))))
        elif handler == "recover_cells_and_kzg_proofs":
            idx, cells = i["cell_indices"], [cell(v) for v in i["cells"]]
            st = st_recover(idx, cells)
            agree(case, st, o)
            out = o and b"".join(hx(v) for v in o[0]) + b"".join(hx(v) for v in o[1])
            f.add(K_RECOVER, case, u64s(idx), blob(b"".join(cells)), result(st, out, CELLS * CELL + CELLS * 48))
        elif handler == "compute_verify_cell_kzg_proof_batch_challenge":
            cs, ps = ([hx(v) for v in i[k]] for k in ("commitments", "proofs"))
            cells = [cell(v) for v in i["cosets_evals"]]
            ci, idx = i["commitment_indices"], i["cell_indices"]
            st = st_cell_challenge(cs, ci, idx, cells, ps)
            agree(case, st, o)
            f.add(K_CELL_CHALLENGE, case, blob(b"".join(cs)), u64s(ci), u64s(idx), blob(b"".join(cells)),
                  blob(b"".join(ps)), result(st, o and hx(o), 32))
        else:
            raise SystemExit(f"kzg.py: unknown handler {handler}")
    f.write()


# ---------------------------------------------------------------- generated cases

def write_generated(lists):
    """TrustedSetup.ofBytes: a list of another length, or a point without the compression bit."""
    f = CaseFile("kzg-generated.bin")
    g1l, g1m, g2m = lists
    add_setup(f, "setup_valid", lists, OK)
    add_setup(f, "setup_lagrange_short", [g1l[:-1], g1m, g2m], INVALID_TRUSTED_SETUP)
    add_setup(f, "setup_lagrange_long", [g1l + g1l[:1], g1m, g2m], INVALID_TRUSTED_SETUP)
    add_setup(f, "setup_monomial_short", [g1l, g1m[:-1], g2m], INVALID_TRUSTED_SETUP)
    add_setup(f, "setup_g2_short", [g1l, g1m, g2m[:-1]], INVALID_TRUSTED_SETUP)
    add_setup(f, "setup_g2_long", [g1l, g1m, g2m + g2m[:1]], INVALID_TRUSTED_SETUP)

    def broken(points, i):
        b = bytearray(points[i])
        b[0] &= 0x7F                       # no compression bit: G1.uncompress and G2.uncompress reject it
        return points[:i] + [bytes(b)] + points[i + 1:]
    add_setup(f, "setup_lagrange_bad_point", [broken(g1l, 100), g1m, g2m], INVALID_TRUSTED_SETUP)
    add_setup(f, "setup_monomial_bad_point", [g1l, broken(g1m, 4095), g2m], INVALID_TRUSTED_SETUP)
    add_setup(f, "setup_g2_bad_point", [g1l, g1m, broken(g2m, 0)], INVALID_TRUSTED_SETUP)
    f.write()


lists = setup_lists()
write_official(lists)
write_generated(lists)
with open(os.path.join(out_dir, "manifest-kzg.txt"), "w") as fh:
    fh.write("\n".join(manifest) + "\n")
