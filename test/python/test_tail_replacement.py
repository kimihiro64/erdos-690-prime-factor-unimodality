"""Guard the certificate-independent CRT branch and its rational margins."""

from __future__ import annotations

from fractions import Fraction as Q
from pathlib import Path

import pytest

from scripts.check_tail_replacement import FORBIDDEN, REQUIRED, check_tail_replacement


def test_solution_excludes_full_record_gap() -> None:
    check_tail_replacement(Path(__file__).resolve().parents[2])


def test_transitive_full_record_import_is_rejected(tmp_path: Path) -> None:
    (tmp_path / "Solution.lean").write_text("import Middle\n")
    (tmp_path / "Middle.lean").write_text(f"public import {FORBIDDEN[1]}Rows.Replay001\n")
    with pytest.raises(ValueError, match="full record-gap replay reached"):
        check_tail_replacement(tmp_path)


def test_comment_does_not_supply_the_replacement(tmp_path: Path) -> None:
    (tmp_path / "Solution.lean").write_text(f"/-\nimport {REQUIRED}\n-/\n")
    with pytest.raises(ValueError, match="does not reach"):
        check_tail_replacement(tmp_path)


def test_uniform_descent_margin_is_positive() -> None:
    v0 = Q(2109, 200)
    alpha = Q(2519, 4910)
    intercept = (
        (1 - alpha) * v0
        - 2 * Q(23557, 10000)
        - Q(2076, 5000)
        - Q(6381, 5000) / (v0 + Q(23, 10)) ** 2
        - Q(1, 380000)
    )
    assert intercept == Q(877288074251, 1231383407380000)
    assert intercept > 0
    assert 1 - alpha - 2 / v0 > 0
    assert 2 - Q(2, 3) - Q(1, 300) - 1 == Q(33, 100)


def test_required_ci_does_not_schedule_full_record_replays() -> None:
    root = Path(__file__).resolve().parents[2]
    workflow = (root / ".github/workflows/ci.yml").read_text()
    assert "  analytic-tail:" in workflow
    assert "+PrimeFactorUnimodality.Proof.CompleteClassificationReduction" in workflow
    assert "scripts/record_gap_ci.py" not in workflow
    assert "record-gap-replay" not in workflow
