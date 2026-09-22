"""Check serial builds for the analytic zero-counting proof, before certificates."""

from pathlib import Path


def test_backlund_foundations_ci_build_order() -> None:
    root = Path(__file__).resolve().parents[2]
    workflow = (root / ".github/workflows/ci.yml").read_text()
    foundations = workflow.split("  lean-foundations:", 1)[1].split("  certificate-prebuild:", 1)[0]
    modules = (
        "PrimeFactorUnimodality.Mathlib.Analysis.Complex.Powers.Recurrence",
        "PrimeFactorUnimodality.Mathlib.Analysis.Complex.JensenCard",
        "PrimeNumberTheoremAnd.Backlund.ZeroCountCrude",
        "PrimeFactorUnimodality.Helpers.Analytic.BacklundAuxiliary",
        "PrimeFactorUnimodality.Helpers.Analytic.BacklundJensen",
        "PrimeFactorUnimodality.Helpers.Analytic.BacklundRealZeros",
    )
    positions = [foundations.index(f"lake build \\\n            +{module}\n") for module in modules]
    assert positions == sorted(positions)
    assert positions[-1] < foundations.index("lake env lean test/lean/BacklundAuxiliary.lean")
