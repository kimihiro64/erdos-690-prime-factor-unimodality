"""Keep scalar xi-summary assembly and its regression coverage wired into CI."""

from pathlib import Path

from scripts.lean_source import lean_imports, strip_lean_comments

ROOT = Path(__file__).resolve().parents[2]
ANALYTIC = "PrimeFactorUnimodality.Helpers.Analytic."


def test_summary_precedes_completeness_in_ci() -> None:
    workflow = (ROOT / ".github/workflows/ci.yml").read_text()
    build = workflow.index(f"+{ANALYTIC}XiBlockSummary\n")
    test = workflow.index("lake env lean test/lean/XiBlockSummary.lean")
    consumer = workflow.index(f"+{ANALYTIC}XiTuringVerification\n")
    assert build < test < consumer


def test_scalar_summaries_retain_actual_rows_and_budget_direction() -> None:
    source = strip_lean_comments(
        (ROOT / "PrimeFactorUnimodality/Helpers/Analytic/XiBlockSummary.lean").read_text()
    )
    assert lean_imports(source) == [f"{ANALYTIC}XiCompletedRows"]
    assert "∃ rows : Fin n → XiSignRow, Valid rows left right" in source
    assert "area ≤ completedAreaRat rows a b" in source
    assert "CountSummary m middle right" in source
    assert "AreaSummary m middle right a b nextArea" in source
    assert "(fun i => (hr.upper i).trans ha)" in source
    assert "(n : \u211a) * (b - a)" in source
    assert "rw [completedAreaRat_append]" in source


def test_summary_reaches_actual_dusart_consumer() -> None:
    source = strip_lean_comments(
        (ROOT / "PrimeFactorUnimodality/Helpers/Analytic/DusartTuringVerification.lean").read_text()
    )
    assert "hasThetaLogSquaredError_of_earlier_band_and_turing_summary" in source
    assert "hsummary.low_criticalLine_of_turing_margin" in source
    assert "hasThetaLogSquaredError_of_earlier_band_and_zero_data finite hgap" in source
    assert "xi_zero_gap_six_of_endpoint_chain hchain hgap p hp" in source


def test_affine_phase_has_analytic_regressions_in_ci() -> None:
    workflow = (ROOT / ".github/workflows/ci.yml").read_text()
    simple = workflow.index("lake env lean test/lean/XiSimplePhase.lean")
    affine = workflow.index(f"+{ANALYTIC}XiAffinePhase\n")
    test = workflow.index("lake env lean test/lean/XiAffinePhase.lean")
    assert simple < affine < test
