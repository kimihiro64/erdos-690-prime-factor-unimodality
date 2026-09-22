"""Keep the theta-table proof infrastructure independent of finite replays."""

from __future__ import annotations

import re
from pathlib import Path

from scripts.lean_source import lean_imports, strip_lean_comments

ROOT = Path(__file__).resolve().parents[2]
ANALYTIC = ROOT / "PrimeFactorUnimodality/Helpers/Analytic"


def test_subinterval_assembler_has_no_generated_dependencies() -> None:
    pending = [
        "PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.Table66Subintervals"
    ]
    visited: set[str] = set()
    while pending:
        module = pending.pop()
        if module in visited:
            continue
        visited.add(module)
        assert ".Generated." not in module
        assert module != "PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows"
        path = ROOT.joinpath(*module.split(".")).with_suffix(".lean")
        if path.is_file():
            pending.extend(lean_imports(strip_lean_comments(path.read_text())))


def test_endpoint_facts_require_covering_cells() -> None:
    code = strip_lean_comments(
        (ANALYTIC / "FinitePrimeIntervalRows/Table66EndpointFacts.lean").read_text()
    )
    assert "cells : ∃ cells : List DusartThetaTable66Cell" in code
    assert "DusartThetaTable66CellsCover data cells" in code
    assert "lower_one_endpoint" not in code
    assert "upper_one_endpoint" not in code


def test_old_first_row_endpoints_are_incompatible() -> None:
    # Lean proves log(200000000) >= 1; even this weaker margin contradicts
    # the simultaneous theta(100000000) upper endpoint requirement.
    assert 200000000 - 550000 > 99998000


def test_table_adapter_keeps_finite_prefix_separate() -> None:
    facts = strip_lean_comments(
        (ANALYTIC / "FinitePrimeIntervalRows/Table66EndpointFacts.lean").read_text()
    )
    assert "(prefix : HasDusartSymmetricThetaBoundsBelow x₀)" in facts
    assert "(cover : ∀ x : Real, x₀ ≤ x → x ≤ X →" in facts
    tail = strip_lean_comments((ANALYTIC / "DusartThetaClosedPart02.lean").read_text())
    assert "(h2x₀.trans hx)" not in tail
    assert "have table : HasDusartSymmetricThetaBoundsBelow X" not in tail


def test_split_theta_modules_have_balanced_scopes() -> None:
    for name in ("DusartThetaClosedPart01.lean", "DusartThetaClosedPart01Tail.lean"):
        code = strip_lean_comments((ANALYTIC / name).read_text())
        assert len(re.findall(r"(?m)^namespace \w+\s*$", code)) == 1
        assert len(re.findall(r"(?m)^noncomputable section\s*$", code)) == 1
        assert len(re.findall(r"(?m)^end(?: [A-Za-z0-9_.]+)?\s*$", code)) == 2


def test_theta_tail_declares_helpers_before_consumers() -> None:
    code = strip_lean_comments((ANALYTIC / "DusartThetaClosedPart01Tail.lean").read_text())
    assert "theorem wangCrapis_explicit_log_derivative_input :" in code
    assert code.index("theorem wangCrapis_thetaBounds_of_logFourthTail") < code.index(
        "theorem wangCrapis_thetaBounds_of_indexed_endpoint_rows_and_tail"
    )
    assert code.index("theorem wangCrapis_thetaBounds_of_paper_ranges_and_prop31_thetaError") < (
        code.index("theorem wangCrapis_thetaBounds_of_table66_and_prop31_thetaError")
    )


def test_ci_checks_subintervals_and_lean_regressions() -> None:
    workflow = (ROOT / ".github/workflows/ci.yml").read_text()
    assert (
        "+PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.Table66Subintervals"
        in (workflow)
    )
    assert "lake env lean test/lean/Table66Subintervals.lean" in workflow
