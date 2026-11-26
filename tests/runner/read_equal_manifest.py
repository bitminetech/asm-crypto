#!/usr/bin/env python3
"""Decode an externally selected SHA-256 proof manifest."""
import base64
import gzip
import os
from pathlib import Path
import sys


def decode(encoded):
    raw = base64.b64decode(encoded, validate=True)
    return gzip.decompress(raw) if raw.startswith(b"\x1f\x8b") else raw


if __name__ == "__main__":
    Path(sys.argv[1]).write_bytes(decode(os.environ["EXPECTED_MANIFEST_B64"]))
