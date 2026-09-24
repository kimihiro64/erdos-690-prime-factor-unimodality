"""Preserve bounded kernel replay and exact endpoint-generator parity."""
# ruff: noqa: RUF001 -- Match Lean's integer type notation exactly.

from __future__ import annotations

import re
from pathlib import Path

import pytest

from scripts.render_record_twin_seed_lean import (
    PRIMES,
    render_lower_residues,
    render_upper_residues,
)

ROOT = Path(__file__).resolve().parents[2]
GENERATED = ROOT / "PrimeFactorUnimodality/Proof/LargeRange/Generated"


@pytest.mark.parametrize("side", ["Lower", "Upper"])
def test_committed_endpoints_match_renderer(side: str) -> None:
    source = (GENERATED / f"RecordTwin{side}Residues.lean").read_text()
    note = re.search(r"/-! (.+) -/", source)
    assert note is not None
    inverses = re.findall(
        rf"apply IsUnit.of_mul_eq_one \(\(([-0-9]+) : ℤ\) : ZMod record{side}\)", source
    )
    assert len(inverses) == len(PRIMES)
    renderer = render_lower_residues if side == "Lower" else render_upper_residues
    assert source == renderer(dict(zip(PRIMES, inverses, strict=True)), note[1])


@pytest.mark.parametrize("side", ["Lower", "Upper"])
def test_all_five_endpoints_use_kernel_arithmetic(side: str) -> None:
    renderer = render_lower_residues if side == "Lower" else render_upper_residues
    source = renderer(dict.fromkeys(PRIMES, "1"), "test provenance")
    assert source.count("  decide +kernel\n") == 5
    assert "  rfl\n" not in source
    assert source.count("  rw [npowRec_eq_npowBinRec]\n") == 5
    assert source.count(f"record{side}_seed_pow]") == 5
    assert f"theorem record{side}_main_kernel" in source
    for prime in PRIMES:
        assert f"theorem record{side}_proper_{prime}_kernel" in source
