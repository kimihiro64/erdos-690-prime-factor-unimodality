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


def test_backlund_argument_ci_build_order() -> None:
    root = Path(__file__).resolve().parents[2]
    workflow = (root / ".github/workflows/ci.yml").read_text()
    foundations = workflow.split("  lean-foundations:", 1)[1].split("  certificate-prebuild:", 1)[0]
    modules = (
        "PrimeFactorUnimodality.Mathlib.Analysis.SpecialFunctions.Trigonometric.ZeroCount",
        "PrimeFactorUnimodality.Mathlib.Analysis.Complex.Log.Interval",
        "PrimeFactorUnimodality.Mathlib.Analysis.Complex.Log.IntervalIntegral",
        "PrimeFactorUnimodality.Helpers.Analytic.BacklundArgument",
        "PrimeFactorUnimodality.Helpers.Analytic.BacklundArgumentIntegral",
    )
    positions = [foundations.index(f"lake build \\\n            +{module}\n") for module in modules]
    assert foundations.index("lake env lean test/lean/BacklundAuxiliary.lean") < positions[0]
    assert positions == sorted(positions)
    assert positions[-1] < foundations.index("lake env lean test/lean/BacklundArgument.lean")


def test_xi_counting_contour_ci_build_order() -> None:
    root = Path(__file__).resolve().parents[2]
    workflow = (root / ".github/workflows/ci.yml").read_text()
    foundations = workflow.split("  lean-foundations:", 1)[1].split("  certificate-prebuild:", 1)[0]
    modules = (
        "PrimeNumberTheoremAnd.RectangleArgumentPrinciple",
        "PrimeFactorUnimodality.Helpers.Analytic.ZetaXiRealNonvanishing",
        "PrimeFactorUnimodality.Helpers.Analytic.XiCountingRectangle",
        "PrimeFactorUnimodality.Helpers.Analytic.XiHalfContour",
        "PrimeFactorUnimodality.Helpers.Analytic.XiRegularHeights",
        "PrimeFactorUnimodality.Helpers.Analytic.BacklundXiLogDerivative",
    )
    positions = [foundations.index(f"lake build \\\n            +{module}\n") for module in modules]
    assert foundations.index("lake env lean test/lean/BacklundArgument.lean") < positions[0]
    assert positions == sorted(positions)
    assert positions[-1] < foundations.index("lake env lean test/lean/XiCountingContour.lean")


def test_xi_counting_decomposition_ci_build_order() -> None:
    root = Path(__file__).resolve().parents[2]
    workflow = (root / ".github/workflows/ci.yml").read_text()
    foundations = workflow.split("  lean-foundations:", 1)[1].split("  certificate-prebuild:", 1)[0]
    contour = foundations.index("lake env lean test/lean/XiCountingContour.lean")
    module = "PrimeFactorUnimodality.Helpers.Analytic.XiCountingDecomposition"
    decomposition = foundations.index(f"lake build \\\n            +{module}\n")
    regression = foundations.index("lake env lean test/lean/XiCountingDecomposition.lean")
    assert contour < decomposition < regression


def test_backlund_vertical_argument_ci_build_order() -> None:
    root = Path(__file__).resolve().parents[2]
    workflow = (root / ".github/workflows/ci.yml").read_text()
    foundations = workflow.split("  lean-foundations:", 1)[1].split("  certificate-prebuild:", 1)[0]
    modules = (
        "PrimeFactorUnimodality.Mathlib.NumberTheory.LSeries.RiemannZetaEulerLog",
        "PrimeFactorUnimodality.Helpers.Analytic.BacklundVerticalArgument",
        "PrimeFactorUnimodality.Helpers.Analytic.BacklundCountingEstimate",
    )
    positions = [foundations.index(f"lake build \\\n            +{module}\n") for module in modules]
    assert foundations.index("lake env lean test/lean/XiCountingDecomposition.lean") < positions[0]
    assert positions == sorted(positions)
    assert positions[-1] < foundations.index(
        "lake env lean test/lean/BacklundVerticalArgument.lean"
    )


def test_gamma_phase_ci_build_order() -> None:
    root = Path(__file__).resolve().parents[2]
    workflow = (root / ".github/workflows/ci.yml").read_text()
    foundations = workflow.split("  lean-foundations:", 1)[1].split("  certificate-prebuild:", 1)[0]
    modules = (
        "PrimeFactorUnimodality.Mathlib.MeasureTheory.Integral.IntervalIntegral.Trapezoid",
        "PrimeFactorUnimodality.Mathlib.Analysis.SpecialFunctions.Complex.LogTrapezoid",
        "PrimeFactorUnimodality.Mathlib.Analysis.SpecialFunctions.Complex.LogShiftLimit",
        "PrimeFactorUnimodality.Helpers.Analytic.GammaLogBranch",
        "PrimeFactorUnimodality.Helpers.Analytic.GammaStirlingPhase",
        "PrimeFactorUnimodality.Helpers.Analytic.XiGammaContour",
        "PrimeFactorUnimodality.Helpers.Analytic.BacklundCountingMainTerm",
    )
    positions = [foundations.index(f"lake build \\\n            +{module}\n") for module in modules]
    assert foundations.index("lake env lean test/lean/BacklundVerticalArgument.lean") < positions[0]
    assert positions == sorted(positions)
    assert positions[-1] < foundations.index("lake env lean test/lean/GammaCountingPhase.lean")


def test_unconditional_high_counting_ci_build_order() -> None:
    root = Path(__file__).resolve().parents[2]
    workflow = (root / ".github/workflows/ci.yml").read_text()
    foundations = workflow.split("  lean-foundations:", 1)[1].split("  certificate-prebuild:", 1)[0]
    modules = (
        "PrimeFactorUnimodality.Mathlib.Analysis.Complex.JensenAverage",
        "PrimeFactorUnimodality.Mathlib.MeasureTheory.Integral.CircleAverageAntipodal",
        "PrimeFactorUnimodality.Helpers.Analytic.BacklundCircleBounds",
        "PrimeFactorUnimodality.Helpers.Analytic.BacklundCircleMean",
        "PrimeFactorUnimodality.Helpers.Analytic.BacklundAveragedJensen",
        "PrimeFactorUnimodality.Helpers.Analytic.BacklundCircleNumerics",
        "PrimeFactorUnimodality.Helpers.Analytic.BacklundCountingHigh",
        "PrimeFactorUnimodality.Helpers.Analytic.XiLehmanHigh",
    )
    positions = [foundations.index(f"lake build \\\n            +{module}\n") for module in modules]
    assert foundations.index("lake env lean test/lean/GammaCountingPhase.lean") < positions[0]
    assert positions == sorted(positions)
    assert positions[-1] < foundations.index("lake env lean test/lean/BacklundCountingHigh.lean")


def test_lehman_master_ci_build_order() -> None:
    root = Path(__file__).resolve().parents[2]
    workflow = (root / ".github/workflows/ci.yml").read_text()
    foundations = workflow.split("  lean-foundations:", 1)[1].split("  certificate-prebuild:", 1)[0]
    modules = (
        "PrimeFactorUnimodality.Helpers.Analytic.XiLehmanBudget",
        "PrimeFactorUnimodality.Helpers.Analytic.KadiriPoleBounds",
        "PrimeFactorUnimodality.Helpers.Analytic.KadiriLehmanMaster",
    )
    positions = [foundations.index(f"lake build \\\n            +{module}\n") for module in modules]
    assert foundations.index("lake env lean test/lean/BacklundCountingHigh.lean") < positions[0]
    assert positions == sorted(positions)
    assert positions[-1] < foundations.index("lake env lean test/lean/XiLehmanBudget.lean")


def test_explicit_gamma_master_ci_build_order() -> None:
    root = Path(__file__).resolve().parents[2]
    workflow = (root / ".github/workflows/ci.yml").read_text()
    foundations = workflow.split("  lean-foundations:", 1)[1].split("  certificate-prebuild:", 1)[0]
    modules = (
        "PrimeFactorUnimodality.Helpers.Analytic.SmoothedGammaBounds",
        "PrimeFactorUnimodality.Helpers.Analytic.KadiriGammaRemainderBounds",
        "PrimeFactorUnimodality.Helpers.Analytic.DigammaEulerIdentity",
        "PrimeFactorUnimodality.Helpers.Analytic.DigammaEulerBounds",
        "PrimeFactorUnimodality.Helpers.Analytic.DigammaLogBounds",
        "PrimeFactorUnimodality.Helpers.Analytic.DigammaRealBounds",
        "PrimeFactorUnimodality.Helpers.Analytic.DigammaHeightBounds",
        "PrimeFactorUnimodality.Helpers.Analytic.SmoothedGammaNormBounds",
        "PrimeFactorUnimodality.Helpers.Analytic.SmoothedGammaRealBounds",
        "PrimeFactorUnimodality.Helpers.Analytic.SmoothedGammaFactorBounds",
        "PrimeFactorUnimodality.Helpers.Analytic.KadiriExplicitMaster",
    )
    positions = [foundations.index(f"lake build \\\n            +{module}\n") for module in modules]
    assert foundations.index("lake env lean test/lean/XiLehmanBudget.lean") < positions[0]
    assert positions == sorted(positions)
    assert positions[-1] < foundations.index("lake env lean test/lean/KadiriGammaBounds.lean")
    assert positions[-1] < foundations.index("lake env lean test/lean/KadiriGammaHeightBounds.lean")
    assert positions[-1] < foundations.index("lake env lean test/lean/KadiriGammaRealBounds.lean")


def test_initial_zero_free_master_ci_build_order() -> None:
    root = Path(__file__).resolve().parents[2]
    workflow = (root / ".github/workflows/ci.yml").read_text()
    foundations = workflow.split("  lean-foundations:", 1)[1].split("  certificate-prebuild:", 1)[0]
    modules = (
        "PrimeFactorUnimodality.Helpers.Analytic.ZetaZeroFreeInitial",
        "PrimeFactorUnimodality.Helpers.Analytic.KadiriOuterSeparation",
        "PrimeFactorUnimodality.Helpers.Analytic.KadiriRegionMaster",
        "PrimeFactorUnimodality.Helpers.Analytic.KadiriInitialMaster",
    )
    positions = [foundations.index(f"lake build \\\n            +{module}\n") for module in modules]
    assert foundations.index("lake env lean test/lean/KadiriGammaBounds.lean") < positions[0]
    assert positions == sorted(positions)
    assert positions[-1] < foundations.index("lake env lean test/lean/KadiriInitialRegion.lean")


def test_bootstrap_budget_ci_build_order() -> None:
    root = Path(__file__).resolve().parents[2]
    workflow = (root / ".github/workflows/ci.yml").read_text()
    foundations = workflow.split("  lean-foundations:", 1)[1].split("  certificate-prebuild:", 1)[0]
    modules = (
        "PrimeFactorUnimodality.Helpers.Analytic.KadiriTransformGap",
        "PrimeFactorUnimodality.Mathlib.Analysis.SpecialFunctions.Integrals.ExpLinear",
        "PrimeFactorUnimodality.Mathlib.Analysis.SpecialFunctions.Integrals.ExpTrig",
        "PrimeFactorUnimodality.Helpers.Analytic.KadiriKernelNormalForm",
        "PrimeFactorUnimodality.Helpers.Analytic.KadiriTransformClosedForm",
        "PrimeFactorUnimodality.Helpers.Analytic.KadiriTransformBounds",
        "PrimeFactorUnimodality.Helpers.Analytic.KadiriBootstrapBudget",
        "PrimeFactorUnimodality.Helpers.Analytic.KadiriGammaBudget",
        "PrimeFactorUnimodality.Helpers.Analytic.KadiriBootstrapCorrection",
        "PrimeFactorUnimodality.Helpers.Analytic.XiLehmanAffine",
        "PrimeFactorUnimodality.Helpers.Analytic.KadiriTailEnvelope",
        "PrimeFactorUnimodality.Helpers.Analytic.KadiriCorrectionEnvelope",
        "PrimeFactorUnimodality.Helpers.Analytic.KadiriMomentEnvelope",
        "PrimeFactorUnimodality.Helpers.Analytic.KadiriCorrectionSign",
        "PrimeFactorUnimodality.Helpers.Analytic.KadiriBootstrapMaster",
    )
    positions = [foundations.index(f"lake build \\\n            +{module}\n") for module in modules]
    assert foundations.index("lake env lean test/lean/KadiriInitialRegion.lean") < positions[0]
    assert positions == sorted(positions)
    assert positions[-1] < foundations.index("lake env lean test/lean/KadiriBootstrap.lean")
    assert positions[-1] < foundations.index("lake env lean test/lean/KadiriMomentEnvelope.lean")
    assert positions[-1] < foundations.index(
        "lake env lean test/lean/KadiriTransformClosedForm.lean"
    )


def test_uniform_bootstrap_ci_build_order() -> None:
    root = Path(__file__).resolve().parents[2]
    workflow = (root / ".github/workflows/ci.yml").read_text()
    foundations = workflow.split("  lean-foundations:", 1)[1].split("  certificate-prebuild:", 1)[0]
    modules = (
        "PrimeFactorUnimodality.Mathlib.Analysis.SpecialFunctions.Trigonometric.Autocorrelation",
        "PrimeFactorUnimodality.Mathlib.Analysis.SpecialFunctions.Log.AffineRatio",
        "PrimeFactorUnimodality.Helpers.Analytic.MossinghoffTrudgianPolynomial",
        "PrimeFactorUnimodality.Helpers.Analytic.KadiriBootstrapParameters",
        "PrimeFactorUnimodality.Helpers.Analytic.KadiriUniformBootstrap",
    )
    positions = [foundations.index(f"lake build \\\n            +{module}\n") for module in modules]
    assert foundations.index("lake env lean test/lean/KadiriMomentEnvelope.lean") < positions[0]
    assert positions == sorted(positions)
    assert positions[-1] < foundations.index(
        "lake env lean test/lean/KadiriPolynomialParameters.lean"
    )


def test_split_bootstrap_ci_build_order() -> None:
    root = Path(__file__).resolve().parents[2]
    workflow = (root / ".github/workflows/ci.yml").read_text()
    foundations = workflow.split("  lean-foundations:", 1)[1].split("  certificate-prebuild:", 1)[0]
    modules = (
        "PrimeFactorUnimodality.Mathlib.Analysis.Calculus.Deriv.EndpointMinimum",
        "PrimeFactorUnimodality.Mathlib.Analysis.Complex.FiniteLaplace.SingleCrossing",
        "PrimeFactorUnimodality.Helpers.Analytic.KadiriTransformMinimum",
        "PrimeFactorUnimodality.Helpers.Analytic.KadiriBootstrapMaster",
        "PrimeFactorUnimodality.Helpers.Analytic.KadiriUniformBootstrap",
        "PrimeFactorUnimodality.Helpers.Analytic.KadiriScaleCoverBootstrap",
        "PrimeFactorUnimodality.Helpers.Analytic.KadiriSplitBootstrap",
        "PrimeFactorUnimodality.Helpers.Analytic.KadiriGridBootstrap",
    )
    positions = [foundations.index(f"lake build \\\n            +{module}\n") for module in modules]
    assert positions == sorted(positions)
    assert positions[-1] < foundations.index("lake env lean test/lean/KadiriSplitBootstrap.lean")
    assert positions[-1] < foundations.index("lake env lean test/lean/KadiriGridBootstrap.lean")


def test_conservative_bootstrap_ci_build_order() -> None:
    root = Path(__file__).resolve().parents[2]
    workflow = (root / ".github/workflows/ci.yml").read_text()
    foundations = workflow.split("  lean-foundations:", 1)[1].split("  certificate-prebuild:", 1)[0]
    modules = (
        "PrimeFactorUnimodality.Helpers.Analytic.KadiriGridBootstrap",
        "PrimeFactorUnimodality.Helpers.Analytic.KadiriConservativeBudget",
        "PrimeFactorUnimodality.Helpers.Analytic.KadiriConservativeBootstrap",
        "PrimeFactorUnimodality.Helpers.Analytic.KadiriElementaryMoments",
        "PrimeFactorUnimodality.Helpers.Analytic.KadiriElementaryBootstrap",
    )
    positions = [foundations.index(f"lake build \\\n            +{module}\n") for module in modules]
    assert positions == sorted(positions)
    assert positions[-1] < foundations.index(
        "lake env lean test/lean/KadiriConservativeBudget.lean"
    )
    assert positions[-1] < foundations.index(
        "lake env lean test/lean/KadiriConservativeBootstrap.lean"
    )
    assert positions[-1] < foundations.index("lake env lean test/lean/KadiriElementaryMoments.lean")
    assert positions[-1] < foundations.index(
        "lake env lean test/lean/KadiriElementaryBootstrap.lean"
    )


def test_psi_smoothing_ci_build_order() -> None:
    root = Path(__file__).resolve().parents[2]
    workflow = (root / ".github/workflows/ci.yml").read_text()
    foundations = workflow.split("  lean-foundations:", 1)[1].split("  certificate-prebuild:", 1)[0]
    modules = (
        "PrimeFactorUnimodality.Mathlib.MeasureTheory.Integral.IntervalIntegral.IteratedAverage",
        "PrimeFactorUnimodality.Helpers.Analytic.DusartPsiSmoothing",
    )
    positions = [foundations.index(f"lake build \\\n            +{module}\n") for module in modules]
    assert positions == sorted(positions)
    assert (
        foundations.index("lake env lean test/lean/KadiriElementaryBootstrap.lean") < positions[0]
    )
    assert positions[-1] < foundations.index("lake env lean test/lean/DusartPsiSmoothing.lean")


def test_box_explicit_formula_ci_build_order() -> None:
    root = Path(__file__).resolve().parents[2]
    workflow = (root / ".github/workflows/ci.yml").read_text()
    foundations = workflow.split("  lean-foundations:", 1)[1].split("  certificate-prebuild:", 1)[0]
    prefix = "PrimeFactorUnimodality.Mathlib.MeasureTheory.Integral.IntervalIntegral"
    modules = (
        f"{prefix}.IteratedAverageRegularity",
        f"{prefix}.IteratedAverageSupport",
        f"{prefix}.IteratedAverageAlgebra",
        "PrimeFactorUnimodality.Helpers.Analytic.DusartBoxCutoff",
        "PrimeFactorUnimodality.Helpers.Analytic.DusartBoxPrimeSum",
        "PrimeFactorUnimodality.Helpers.Analytic.DusartBoxExplicitFormula",
        "PrimeFactorUnimodality.Helpers.Analytic.DusartBoxAverageFormula",
    )
    positions = [foundations.index(f"lake build \\\n            +{module}\n") for module in modules]
    assert positions == sorted(positions)
    for test in ("IteratedBoxAverage", "DusartBoxCutoff", "DusartBoxAverageFormula"):
        assert positions[-1] < foundations.index(f"lake env lean test/lean/{test}.lean")


def test_box_spectral_formula_ci_build_order() -> None:
    root = Path(__file__).resolve().parents[2]
    workflow = (root / ".github/workflows/ci.yml").read_text()
    foundations = workflow.split("  lean-foundations:", 1)[1].split("  certificate-prebuild:", 1)[0]
    prefix = "PrimeFactorUnimodality.Mathlib.MeasureTheory.Integral.IntervalIntegral"
    analytic = "PrimeFactorUnimodality.Helpers.Analytic"
    modules = (
        "PrimeFactorUnimodality.Mathlib.Analysis.SpecialFunctions.Pow.ComplexDecay",
        f"{prefix}.IteratedAverageContinuous",
        f"{prefix}.IteratedAverageComplex",
        f"{analytic}.DusartBoxDistributionIntegral",
        f"{analytic}.DusartBoxPrimitiveTransform",
        f"{analytic}.DusartBoxComplexTransform",
        f"{analytic}.DusartBoxPowerTransform",
        f"{analytic}.DusartBoxMainTerm",
        f"{analytic}.DusartBoxZeroBounds",
        f"{analytic}.DusartBoxSpectralFormula",
    )
    positions = [foundations.index(f"lake build \\\n            +{module}\n") for module in modules]
    assert positions == sorted(positions)
    assert foundations.index("lake env lean test/lean/DusartBoxAverageFormula.lean") < positions[0]
    for test in ("IteratedComplexBoxAverage", "DusartBoxSpectralFormula"):
        assert positions[-1] < foundations.index(f"lake env lean test/lean/{test}.lean")


def test_box_high_tail_ci_build_order() -> None:
    root = Path(__file__).resolve().parents[2]
    workflow = (root / ".github/workflows/ci.yml").read_text()
    foundations = workflow.split("  lean-foundations:", 1)[1].split("  certificate-prebuild:", 1)[0]
    prefix = "PrimeFactorUnimodality.Mathlib.MeasureTheory.Integral.IntervalIntegral"
    analytic = "PrimeFactorUnimodality.Helpers.Analytic"
    modules = (
        "PrimeFactorUnimodality.Mathlib.Analysis.Calculus.Deriv.ForwardDiff",
        "PrimeFactorUnimodality.Mathlib.Analysis.SpecialFunctions.Pow.IteratedPrimitive",
        f"{prefix}.IteratedAverageLocal",
        f"{prefix}.IteratedAveragePrimitive",
        f"{prefix}.IteratedAveragePower",
        f"{analytic}.DusartBoxHeightDecay",
        f"{analytic}.XiHeightTailZeroHigh",
        f"{analytic}.DusartBoxHighTail",
        f"{analytic}.DusartBoxZeroSplit",
    )
    positions = [foundations.index(f"+{module}\n") for module in modules]
    assert positions == sorted(positions)
    assert foundations.index("lake env lean test/lean/DusartBoxSpectralFormula.lean") < positions[0]
    for test in ("IteratedPowerAverages", "DusartBoxHighTail"):
        assert positions[-1] < foundations.index(f"lake env lean test/lean/{test}.lean")


def test_main_ci_preserves_running_proof_build() -> None:
    root = Path(__file__).resolve().parents[2]
    workflow = (root / ".github/workflows/ci.yml").read_text()
    concurrency = workflow.split("concurrency:\n", 1)[1].split("\njobs:\n", 1)[0]
    assert "group: ${{ github.workflow }}-${{ github.ref }}" in concurrency
    assert "cancel-in-progress: ${{ github.ref != 'refs/heads/main' }}" in concurrency
