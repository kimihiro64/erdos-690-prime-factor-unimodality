"""Extract small, scope-qualified resource evidence without publishing local research trees.

Input is a directory of archived measurement reports. This does not rerun any
certificate and does not turn numerical screens into formal mathematical facts.
"""

from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
from typing import Any


def summary(directory: Path) -> dict[str, Any]:
    reports: dict[str, Any] = {}
    hashes: dict[str, str] = {}
    for name in (
        "primality-feasibility.json",
        "sieve-packed-count-report.json",
        "packed-convolution-report.json",
        "three-billion-count-replay-estimate.json",
        "external-zero-signs-report.json",
        "platt-errors-170m-report.json",
        "xi-end-to-end-profile8/report.json",
    ):
        source = directory / name
        hashes[name] = hashlib.sha256(source.read_bytes()).hexdigest()
        reports[name] = json.loads(source.read_text())
    primality = [
        {key: row[key] for key in ("test", "seconds", "targets", "source_bytes")}
        for row in reports["primality-feasibility.json"]
    ]
    sieve = reports["sieve-packed-count-report.json"]
    convolution = reports["packed-convolution-report.json"]
    meissel = reports["three-billion-count-replay-estimate.json"]
    external = reports["external-zero-signs-report.json"]
    platt = reports["platt-errors-170m-report.json"]
    scenario = next(
        row for row in platt["rows"][0]["best"] if row["B"] == 16384 and row["J"] == 7803
    )
    xi = reports["xi-end-to-end-profile8/report.json"]
    return {
        "scope": "Selected historical component evidence, NOT a whole-Dusart runtime forecast.",
        "host": "Two AArch64 Neoverse-N1 cores; single-run wall times with warm dependencies.",
        "revision_limitations": "The Xi generated source digest is recorded below. Full experiment "
        "commits were not recorded in the other reports; do not infer them from the release "
        "commit. Report hashes identify the source evidence, not independently reproducible "
        "benchmark inputs.",
        "report_sha256": hashes,
        "primality": {
            "kind": "measurement",
            "scope": "Individual certificates, not counting "
            "completeness; includes import/process cost.",
            "rows": primality,
        },
        "packed_count": {
            "kind": "measurement",
            "scope": sieve["warning"],
            "rows": [
                {
                    key: row[key]
                    for key in ("count", "seconds", "olean_bytes", "peak_sampled_rss_kib")
                }
                for row in sieve["reports"]
            ],
        },
        "packed_convolution": {
            "kind": "measurement",
            "scope": convolution["warning"],
            "rows": [
                {key: row[key] for key in ("count", "seconds", "source_bytes")}
                for row in convolution["reports"]
            ],
        },
        "meissel": {
            "kind": "projection",
            "scope": meissel["warning"],
            **{
                key: meissel[key]
                for key in (
                    "limit",
                    "method",
                    "projected_rows",
                    "check_rows_per_second",
                    "checking_days",
                    "data_elaboration_days",
                    "check_plus_data_days",
                    "predicted_source_gib",
                )
            },
        },
        "external_signs": {
            "kind": "external measurement, not Lean checking",
            "scope": external["warning"],
            "precision": external["precision"],
            "python_flint": external["python_flint"],
            "rows": [
                {
                    key: row[key]
                    for key in (
                        "height",
                        "sign_samples",
                        "external_endpoint_sign_seconds",
                        "external_zero_search_seconds",
                    )
                }
                for row in external["rows"]
            ],
        },
        "platt_scenario": {
            "kind": "nonrigorous workload screen",
            "scope": platt["warning"],
            **{
                key: scenario[key]
                for key in (
                    "height",
                    "A",
                    "B",
                    "J",
                    "K",
                    "windows",
                    "complex_convolutions",
                    "convolution_input_cells",
                    "moment_cells",
                )
            },
        },
        "xi_low_block": {
            "kind": "measurement",
            "scope": xi["scope"],
            "parameters": xi["parameters"],
            "source_sha256": xi["source_sha256"],
            "seconds": xi["checking"]["seconds"],
            "olean_bytes": xi["olean_bytes"],
            "limitations": xi["limitations"],
        },
    }


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("reports", type=Path)
    parser.add_argument("output", type=Path)
    args = parser.parse_args()
    args.output.write_text(json.dumps(summary(args.reports), indent=2) + "\n")


if __name__ == "__main__":
    main()
