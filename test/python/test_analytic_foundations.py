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


def test_smoothed_laplace_ci_build_order() -> None:
    root = Path(__file__).resolve().parents[2]
    workflow = (root / ".github/workflows/ci.yml").read_text()
    foundations = workflow.split("  lean-foundations:", 1)[1].split("  certificate-prebuild:", 1)[0]
    modules = (
        "Mathlib.Analysis.Complex.FiniteLaplace.Basic",
        "Mathlib.Analysis.Complex.FiniteLaplace.Bounds",
        "Mathlib.Analysis.Complex.FiniteLaplace.Summability",
        "Helpers.Analytic.SmoothedXiRemainder",
    )
    positions = [
        foundations.index(f"lake build \\\n            +PrimeFactorUnimodality.{module}")
        for module in modules
    ]
    assert positions == sorted(positions)
    assert positions[-1] < foundations.index("lake env lean test/lean/SmoothedLaplace.lean")


def test_smoothed_gamma_ci_build_order() -> None:
    root = Path(__file__).resolve().parents[2]
    workflow = (root / ".github/workflows/ci.yml").read_text()
    foundations = workflow.split("  lean-foundations:", 1)[1].split("  certificate-prebuild:", 1)[0]
    modules = (
        "Mathlib.Analysis.Complex.FiniteLaplace.Continuity",
        "Mathlib.Analysis.SpecialFunctions.Integrability.LogCauchy",
        "Helpers.Analytic.DigammaLowerBound",
        "Helpers.Analytic.SmoothedGammaRemainder",
    )
    positions = [
        foundations.index(f"lake build \\\n            +PrimeFactorUnimodality.{module}")
        for module in modules
    ]
    assert positions == sorted(positions)
    assert positions[-1] < foundations.index("lake env lean test/lean/SmoothedGamma.lean")


def test_smoothed_inversion_ci_build_order() -> None:
    root = Path(__file__).resolve().parents[2]
    workflow = (root / ".github/workflows/ci.yml").read_text()
    foundations = workflow.split("  lean-foundations:", 1)[1].split("  certificate-prebuild:", 1)[0]
    modules = (
        "Mathlib.Analysis.Complex.FiniteLaplace.RemainderSource",
        "Mathlib.Analysis.Complex.Integrability.Cauchy",
        "Mathlib.Analysis.Complex.FiniteLaplace.Inversion",
        "Mathlib.NumberTheory.LSeries.VerticalIntegral",
        "Mathlib.Analysis.Complex.FiniteLaplace.DirichletIntegral",
        "Helpers.Analytic.SmoothedPrimeIntegral",
    )
    positions = [
        foundations.index(f"lake build \\\n            +PrimeFactorUnimodality.{module}")
        for module in modules
    ]
    assert positions == sorted(positions)
    assert positions[-1] < foundations.index("lake env lean test/lean/SmoothedInversion.lean")


def test_smoothed_xi_ci_build_order() -> None:
    root = Path(__file__).resolve().parents[2]
    workflow = (root / ".github/workflows/ci.yml").read_text()
    foundations = workflow.split("  lean-foundations:", 1)[1].split("  certificate-prebuild:", 1)[0]
    modules = (
        "Mathlib.Analysis.SpecialFunctions.Pow.ThreeHalves",
        "Mathlib.MeasureTheory.Integral.Bochner.Series",
        "Mathlib.Analysis.Complex.Integrability.Resolvent",
        "Mathlib.Analysis.Complex.Hadamard.IntegralBounds",
        "Mathlib.Analysis.Complex.Hadamard.Integral",
        "Mathlib.Analysis.Complex.FiniteLaplace.ContourBounds",
        "Mathlib.Analysis.Complex.FiniteLaplace.ResolventIntegral",
        "Helpers.Analytic.XiHadamardIntegral",
        "Helpers.Analytic.SmoothedXiInterchange",
    )
    positions = [
        foundations.index(f"lake build \\\n            +PrimeFactorUnimodality.{module}")
        for module in modules
    ]
    assert positions == sorted(positions)
    assert positions[4] < foundations.index("lake env lean test/lean/HadamardIntegral.lean")
    assert positions[-1] < foundations.index("lake env lean test/lean/SmoothedInversion.lean")
