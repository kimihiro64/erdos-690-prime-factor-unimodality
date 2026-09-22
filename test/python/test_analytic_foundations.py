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


def test_smoothed_explicit_formula_ci_build_order() -> None:
    root = Path(__file__).resolve().parents[2]
    workflow = (root / ".github/workflows/ci.yml").read_text()
    foundations = workflow.split("  lean-foundations:", 1)[1].split("  certificate-prebuild:", 1)[0]
    modules = (
        "Helpers.Analytic.SmoothedPrimeIntegral",
        "Helpers.Analytic.SmoothedXiInterchange",
        "Helpers.Analytic.DigammaHadamard",
        "Helpers.Analytic.DigammaHadamardIntegral",
        "Helpers.Analytic.SmoothedDigammaIntegral",
        "Helpers.Analytic.ZetaContourDecomposition",
        "Helpers.Analytic.SmoothedExplicitFormula",
    )
    positions = [
        foundations.index(f"lake build \\\n            +PrimeFactorUnimodality.{module}")
        for module in modules
    ]
    assert positions == sorted(positions)
    assert positions[-1] < foundations.index("lake env lean test/lean/SmoothedInversion.lean")


def test_smoothed_gamma_boundary_ci_build_order() -> None:
    root = Path(__file__).resolve().parents[2]
    workflow = (root / ".github/workflows/ci.yml").read_text()
    foundations = workflow.split("  lean-foundations:", 1)[1].split("  certificate-prebuild:", 1)[0]
    modules = (
        "Mathlib.Analysis.Complex.Integrability.RightResolvent",
        "Mathlib.Analysis.Complex.FiniteLaplace.RightResolventIntegral",
        "Mathlib.Analysis.Complex.FiniteLaplace",
        "Mathlib.Analysis.SpecialFunctions.Gamma.DigammaConjugation",
        "Helpers.Analytic.SmoothedDigammaReflection",
        "Helpers.Analytic.SmoothedRealDigammaIntegral",
        "Helpers.Analytic.SmoothedGammaBoundary",
    )
    positions = [
        foundations.index(f"lake build \\\n            +PrimeFactorUnimodality.{module}\n")
        for module in modules
    ]
    assert positions == sorted(positions)
    assert positions[-1] < foundations.index("lake env lean test/lean/SmoothedInversion.lean")


def test_smoothed_continuation_ci_build_order() -> None:
    root = Path(__file__).resolve().parents[2]
    workflow = (root / ".github/workflows/ci.yml").read_text()
    foundations = workflow.split("  lean-foundations:", 1)[1].split("  certificate-prebuild:", 1)[0]
    modules = (
        "Mathlib.Analysis.Complex.FiniteLaplace.Differentiability",
        "Mathlib.Analysis.Complex.FiniteLaplace.PairedBounds",
        "Mathlib.Analysis.Complex.FiniteLaplace.PairedSeries",
        "Mathlib.Analysis.Complex.FiniteLaplace",
        "Helpers.Analytic.ZetaXiDivisorReflection",
        "Helpers.Analytic.ZetaXiHadamardConstant",
        "Helpers.Analytic.SmoothedPairedSums",
        "Helpers.Analytic.SmoothedPairedEvaluation",
        "Helpers.Analytic.SmoothedPrimeEntire",
        "Helpers.Analytic.SmoothedEntireFormula",
        "Helpers.Analytic.SmoothedRealExplicitFormula",
    )
    positions = [
        foundations.index(f"lake build \\\n            +PrimeFactorUnimodality.{module}\n")
        for module in modules
    ]
    assert positions == sorted(positions)
    assert positions[-1] < foundations.index("lake env lean test/lean/SmoothedInversion.lean")


def test_kadiri_weight_ci_build_order() -> None:
    root = Path(__file__).resolve().parents[2]
    workflow = (root / ".github/workflows/ci.yml").read_text()
    foundations = workflow.split("  lean-foundations:", 1)[1].split("  certificate-prebuild:", 1)[0]
    modules = (
        "SmoothedRealExplicitFormula",
        "SmoothedStechkinFormula",
        "KadiriWeightKernel",
        "KadiriWeightEndpoints",
        "KadiriCorrelation",
        "KadiriWeight",
        "KadiriWeightPositivity",
        "KadiriDerivativeBound",
        "KadiriLaplaceBounds",
        "KadiriWeightExplicitFormula",
        "KadiriStechkin",
    )
    positions = [
        foundations.index(
            f"lake build \\\n            +PrimeFactorUnimodality.Helpers.Analytic.{module}\n"
        )
        for module in modules
    ]
    assert positions == sorted(positions)
    assert positions[1] < foundations.index("lake env lean test/lean/SmoothedInversion.lean")
    assert positions[-2] < foundations.index("lake env lean test/lean/KadiriWeight.lean")
    assert positions[-1] < foundations.index("lake env lean test/lean/KadiriPositivity.lean")
    for candidate in ("CosineCorrelation", "CorrelationBound"):
        candidate_build = foundations.index(
            "lake build \\\n            +PrimeFactorUnimodality.Mathlib."
            f"Analysis.SpecialFunctions.Integrals.{candidate}\n"
        )
        assert candidate_build < positions[2]


def test_laplace_positivity_ci_build_order() -> None:
    root = Path(__file__).resolve().parents[2]
    workflow = (root / ".github/workflows/ci.yml").read_text()
    foundations = workflow.split("  lean-foundations:", 1)[1].split("  certificate-prebuild:", 1)[0]
    modules = (
        "Mathlib.MeasureTheory.Integral.IntervalIntegral.Triangle",
        "Mathlib.Analysis.Complex.FiniteLaplace.VolterraEnergy",
        "Mathlib.Analysis.Complex.FiniteLaplace.Correlation",
        "Mathlib.Analysis.Complex.FiniteLaplace.Scaling",
        "Helpers.Analytic.KadiriLaplacePositivity",
    )
    positions = [
        foundations.index(f"lake build \\\n            +PrimeFactorUnimodality.{module}\n")
        for module in modules
    ]
    assert positions == sorted(positions)
    assert positions[-1] < foundations.index("lake env lean test/lean/KadiriLaplacePositivity.lean")


def test_paired_zero_ci_build_order() -> None:
    root = Path(__file__).resolve().parents[2]
    workflow = (root / ".github/workflows/ci.yml").read_text()
    foundations = workflow.split("  lean-foundations:", 1)[1].split("  certificate-prebuild:", 1)[0]
    modules = (
        "Helpers.Analytic.KadiriLaplacePositivity",
        "Mathlib.Analysis.Complex.PhragmenLindelof.RealPart",
        "Mathlib.Analysis.Complex.FiniteLaplace.RealSource",
        "Mathlib.Analysis.Complex.FiniteLaplace.PairedStrip",
        "Mathlib.Analysis.Complex.Poisson.ThreeKernel",
        "Mathlib.Analysis.Complex.Poisson.ThreeKernelUniform",
        "Helpers.Analytic.KadiriPairedStrip",
        "Helpers.Analytic.KadiriPairParameters",
        "Helpers.Analytic.KadiriPairedZeros",
    )
    positions = [
        foundations.index(f"lake build \\\n            +PrimeFactorUnimodality.{module}\n")
        for module in modules
    ]
    assert positions == sorted(positions)
    assert positions[-1] < foundations.index("lake env lean test/lean/KadiriPairedZeros.lean")


def test_zero_sum_ci_build_order() -> None:
    root = Path(__file__).resolve().parents[2]
    workflow = (root / ".github/workflows/ci.yml").read_text()
    foundations = workflow.split("  lean-foundations:", 1)[1].split("  certificate-prebuild:", 1)[0]
    modules = (
        "Helpers.Analytic.KadiriStechkin",
        "Mathlib.Analysis.Analytic.Order.Conjugation",
        "Mathlib.Topology.Algebra.InfiniteSum.Paired",
        "Helpers.Analytic.ZetaXiDivisorConjugation",
        "Helpers.Analytic.ZetaXiDivisorPairing",
        "Helpers.Analytic.KadiriZeroSummability",
        "Helpers.Analytic.KadiriZeroSums",
        "Helpers.Analytic.KadiriOuterMaster",
    )
    positions = [
        foundations.index(f"lake build \\\n            +PrimeFactorUnimodality.{module}\n")
        for module in modules
    ]
    assert positions == sorted(positions)
    assert positions[-1] < foundations.index("lake env lean test/lean/KadiriZeroSums.lean")


def test_retained_zero_ci_build_order() -> None:
    root = Path(__file__).resolve().parents[2]
    workflow = (root / ".github/workflows/ci.yml").read_text()
    foundations = workflow.split("  lean-foundations:", 1)[1].split("  certificate-prebuild:", 1)[0]
    modules = (
        "Mathlib.Analysis.Complex.FiniteLaplace.Monotonicity",
        "Mathlib.Analysis.Complex.FiniteLaplace",
        "Helpers.Analytic.KadiriZeroSums",
        "Helpers.Analytic.KadiriRetainedZeros",
        "Helpers.Analytic.KadiriRetainedMaster",
        "Helpers.Analytic.KadiriRetainedBounds",
        "Helpers.Analytic.KadiriDistinguishedZero",
    )
    positions = [
        foundations.index(f"lake build \\\n            +PrimeFactorUnimodality.{module}\n")
        for module in modules
    ]
    assert positions == sorted(positions)
    assert positions[-1] < foundations.index("lake env lean test/lean/KadiriRetainedZero.lean")


def test_weighted_remainder_ci_build_order() -> None:
    root = Path(__file__).resolve().parents[2]
    workflow = (root / ".github/workflows/ci.yml").read_text()
    foundations = workflow.split("  lean-foundations:", 1)[1].split("  certificate-prebuild:", 1)[0]
    modules = (
        "Mathlib.Analysis.Complex.FiniteLaplace.Monotonicity",
        "Mathlib.Analysis.Complex.FiniteLaplace.WeightedBounds",
        "Mathlib.Analysis.Complex.FiniteLaplace",
        "Mathlib.Analysis.SpecialFunctions.Exp.Cubic",
        "Mathlib.Analysis.SpecialFunctions.Integrals.ExpMoments",
        "Helpers.Analytic.KadiriDerivativeMass",
        "Helpers.Analytic.KadiriWeightedRemainder",
        "Helpers.Analytic.KadiriDerivativeMoments",
        "Helpers.Analytic.KadiriOuterPairRemainder",
    )
    positions = [
        foundations.index(f"lake build \\\n            +PrimeFactorUnimodality.{module}\n")
        for module in modules
    ]
    assert positions == sorted(positions)
    assert positions[-1] < foundations.index("lake env lean test/lean/KadiriWeightedRemainder.lean")


def test_outer_tail_ci_build_order() -> None:
    root = Path(__file__).resolve().parents[2]
    workflow = (root / ".github/workflows/ci.yml").read_text()
    foundations = workflow.split("  lean-foundations:", 1)[1].split("  certificate-prebuild:", 1)[0]
    modules = (
        "Helpers.Analytic.KadiriDistinguishedZero",
        "Helpers.Analytic.KadiriOuterPairRemainder",
        "Mathlib.Analysis.Complex.Poisson.OuterStrip",
        "Mathlib.Analysis.Complex.Series.Imaginary",
        "Helpers.Analytic.KadiriOuterPairs",
        "Helpers.Analytic.XiHeightTail",
        "Helpers.Analytic.KadiriOuterTail",
        "Helpers.Analytic.KadiriTailMaster",
    )
    positions = [
        foundations.index(f"lake build \\\n            +PrimeFactorUnimodality.{module}\n")
        for module in modules
    ]
    assert positions == sorted(positions)
    assert positions[-1] < foundations.index("lake env lean test/lean/KadiriOuterTail.lean")


def test_height_tail_mass_ci_build_order() -> None:
    root = Path(__file__).resolve().parents[2]
    workflow = (root / ".github/workflows/ci.yml").read_text()
    foundations = workflow.split("  lean-foundations:", 1)[1].split("  certificate-prebuild:", 1)[0]
    modules = (
        "Helpers.Analytic.KadiriTailMaster",
        "Mathlib.Analysis.Complex.Poisson.Reciprocal",
        "Mathlib.Analysis.SpecialFunctions.Integrals.ReciprocalSquarePair",
        "Helpers.Analytic.XiHeightTailPairing",
        "Helpers.Analytic.XiLowReciprocalMass",
        "Helpers.Analytic.XiHeightTailZero",
        "Helpers.Analytic.XiHeightTailEndpoint",
        "Helpers.Analytic.XiLehmanIntegral",
        "Mathlib.Analysis.SpecialFunctions.Integrals.LogReciprocalSquarePair",
        "Helpers.Analytic.XiLehmanMainIntegral",
    )
    positions = [
        foundations.index(f"lake build \\\n            +PrimeFactorUnimodality.{module}\n")
        for module in modules
    ]
    assert positions == sorted(positions)
    assert positions[-1] < foundations.index("lake env lean test/lean/XiHeightTail.lean")


def test_xi_counting_abel_ci_build_order() -> None:
    root = Path(__file__).resolve().parents[2]
    workflow = (root / ".github/workflows/ci.yml").read_text()
    foundations = workflow.split("  lean-foundations:", 1)[1].split("  certificate-prebuild:", 1)[0]
    modules = (
        "Helpers.Analytic.XiLehmanMainIntegral",
        "Mathlib.MeasureTheory.Integral.FinsetAbel",
        "Helpers.Analytic.XiZeroCountingAbel",
        "Helpers.Analytic.XiZeroCountingRemainder",
    )
    positions = [
        foundations.index(f"lake build \\\n            +PrimeFactorUnimodality.{module}\n")
        for module in modules
    ]
    assert positions == sorted(positions)
    assert positions[-1] < foundations.index("lake env lean test/lean/XiZeroCounting.lean")


def test_xi_counting_tail_ci_build_order() -> None:
    root = Path(__file__).resolve().parents[2]
    workflow = (root / ".github/workflows/ci.yml").read_text()
    foundations = workflow.split("  lean-foundations:", 1)[1].split("  certificate-prebuild:", 1)[0]
    modules = (
        "Helpers.Analytic.XiZeroCountingRemainder",
        "Mathlib.Topology.Algebra.InfiniteSum.Sublevel",
        "Helpers.Analytic.XiZeroCountingLimits",
        "Helpers.Analytic.XiZeroCountingImproper",
        "Mathlib.Analysis.SpecialFunctions.Integrals.ReciprocalSquarePairDeriv",
        "Helpers.Analytic.XiLehmanAbel",
    )
    positions = [
        foundations.index(f"lake build \\\n            +PrimeFactorUnimodality.{module}\n")
        for module in modules
    ]
    assert positions == sorted(positions)
    assert positions[-1] < foundations.index("lake env lean test/lean/XiZeroCountingTail.lean")


def test_xi_lehman_remainder_ci_build_order() -> None:
    root = Path(__file__).resolve().parents[2]
    workflow = (root / ".github/workflows/ci.yml").read_text()
    foundations = workflow.split("  lean-foundations:", 1)[1].split("  certificate-prebuild:", 1)[0]
    modules = (
        "Helpers.Analytic.XiLehmanAbel",
        "Mathlib.MeasureTheory.Integral.IoiTranslation",
        "Mathlib.Analysis.SpecialFunctions.Integrals.ReciprocalSquarePairWeighted",
        "Helpers.Analytic.XiLehmanSmoothTerm",
        "Helpers.Analytic.XiLehmanRemainder",
    )
    positions = [
        foundations.index(f"lake build \\\n            +PrimeFactorUnimodality.{module}\n")
        for module in modules
    ]
    assert positions == sorted(positions)
    assert positions[-1] < foundations.index("lake env lean test/lean/XiLehmanRemainder.lean")


def test_xi_zeta_counting_bridge_ci_build_order() -> None:
    root = Path(__file__).resolve().parents[2]
    workflow = (root / ".github/workflows/ci.yml").read_text()
    foundations = workflow.split("  lean-foundations:", 1)[1].split("  certificate-prebuild:", 1)[0]
    modules = (
        "XiLehmanRemainder",
        "XiZeroCountingEndpoints",
        "ZetaXiMultiplicity",
        "XiZetaCountingBridge",
        "XiZetaCountingBounds",
    )
    positions = [
        foundations.index(
            f"lake build \\\n            +PrimeFactorUnimodality.Helpers.Analytic.{module}\n"
        )
        for module in modules
    ]
    assert positions == sorted(positions)
    assert positions[-1] < foundations.index("lake env lean test/lean/XiZetaCountingBridge.lean")
