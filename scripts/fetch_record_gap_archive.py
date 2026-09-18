#!/usr/bin/env python3
"""Recover and verify the published 1,113,106 prime-gap archives.

The original site is no longer serving the file.  Common Crawl captured the
HTTP response in August 2018, so this script fetches the pinned WARC byte range,
extracts the ZIP payload, and verifies the archive hash before writing it.
"""

from __future__ import annotations

import argparse
import gzip
import hashlib
import urllib.request
from pathlib import Path
from typing import TypedDict


class Artifact(TypedDict):
    warc: str
    offset: int
    warc_length: int
    zip_length: int
    sha256: str


COMMON_CRAWL_PREFIX = (
    "https://data.commoncrawl.org/crawl-data/CC-MAIN-2018-34/segments/1534221209165.16/warc/"
)
ARTIFACTS: dict[str, Artifact] = {
    "factors": {
        "warc": "CC-MAIN-20180814150733-20180814170733-00631.warc.gz",
        "offset": 344_298_956,
        "warc_length": 108_151,
        "zip_length": 107_375,
        "sha256": "764ff7ee9c7c8e823d8959c1d8b4b05cdb7af2739c2ca8a3ba18bcb357f422ad",
    },
    "residues": {
        "warc": "CC-MAIN-20180814150733-20180814170733-00507.warc.gz",
        "offset": 333_152_286,
        "warc_length": 212_520,
        "zip_length": 211_731,
        "sha256": "4bf239672c0d9a293f837bbc424c1bcd488940ed654297d44a2014ce37bb2346",
    },
}


def sha256(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def fetch_payload(kind: str) -> bytes:
    artifact = ARTIFACTS[kind]
    offset = artifact["offset"]
    warc_length = artifact["warc_length"]
    request = urllib.request.Request(
        COMMON_CRAWL_PREFIX + str(artifact["warc"]),
        headers={"Range": f"bytes={offset}-{offset + warc_length - 1}"},
    )
    with urllib.request.urlopen(request, timeout=120) as response:
        compressed = response.read()
    if len(compressed) != warc_length:
        raise ValueError(f"expected {warc_length} WARC bytes, received {len(compressed)}")
    warc = gzip.decompress(compressed)
    zip_start = warc.index(b"PK\x03\x04")
    zip_length = artifact["zip_length"]
    return warc[zip_start : zip_start + zip_length]


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--kind", choices=sorted(ARTIFACTS), default="factors")
    parser.add_argument("output", type=Path)
    args = parser.parse_args()

    payload = fetch_payload(args.kind)
    digest = sha256(payload)
    expected_digest = str(ARTIFACTS[args.kind]["sha256"])
    if digest != expected_digest:
        raise ValueError(f"archive SHA-256 mismatch: {digest}")
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_bytes(payload)
    print(f"wrote {args.output} ({len(payload)} bytes, sha256={digest})")


if __name__ == "__main__":
    main()
