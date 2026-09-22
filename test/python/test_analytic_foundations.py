"""Keep independent analytic candidates ahead of their consumers and regressions."""

from pathlib import Path


def test_stechkin_ci_build_order() -> None:
    root = Path(__file__).resolve().parents[2]
    workflow = (root / ".github/workflows/ci.yml").read_text()
    foundations = workflow.split("  lean-foundations:", 1)[1].split("  certificate-prebuild:", 1)[0]
    modules = (
        "Mathlib.Analysis.Complex.Poisson.Stechkin",
        "Mathlib.NumberTheory.LSeries.ZetaTrigonometricShift",
        "Helpers.Analytic.StechkinBasic",
        "Helpers.Analytic.ZetaXiStechkin",
        "Helpers.Analytic.ZetaXiStechkinZero",
    )
    positions = [
        foundations.index(f"lake build \\\n            +PrimeFactorUnimodality.{module}")
        for module in modules
    ]
    assert positions == sorted(positions)
    assert positions[-1] < foundations.index("lake env lean test/lean/Stechkin.lean")
