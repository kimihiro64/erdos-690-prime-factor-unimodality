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


def test_box_corrections_ci_build_order() -> None:
    root = Path(__file__).resolve().parents[2]
    workflow = (root / ".github/workflows/ci.yml").read_text()
    foundations = workflow.split("  lean-foundations:", 1)[1].split("  certificate-prebuild:", 1)[0]
    prefix = "PrimeFactorUnimodality.Helpers.Analytic"
    modules = (
        f"{prefix}.DusartBoxGammaBounds",
        f"{prefix}.DusartBoxPsiError",
        f"{prefix}.DusartBoxPsiBudget",
        f"{prefix}.ThetaFromPsi",
        f"{prefix}.DusartBoxLogFourth",
    )
    positions = [foundations.index(f"+{module}\n") for module in modules]
    assert positions == sorted(positions)
    assert foundations.index("lake env lean test/lean/DusartBoxHighTail.lean") < positions[0]
    for test in ("DusartBoxCorrections", "DusartBoxPsiBudget", "DusartBoxLogFourth"):
        assert positions[-1] < foundations.index(f"lake env lean test/lean/{test}.lean")


def test_reciprocal_norm_ci_build_order() -> None:
    root = Path(__file__).resolve().parents[2]
    workflow = (root / ".github/workflows/ci.yml").read_text()
    foundations = workflow.split("  lean-foundations:", 1)[1].split("  certificate-prebuild:", 1)[0]
    prefix = "PrimeFactorUnimodality.Helpers.Analytic"
    modules = (
        f"{prefix}.XiReciprocalNormWindow",
        f"{prefix}.XiReciprocalCountIntegral",
        f"{prefix}.XiReciprocalNormHigh",
        f"{prefix}.XiReciprocalNormSymmetry",
        f"{prefix}.XiLowReciprocalNormBound",
        f"{prefix}.DusartBoxCountingBudget",
    )
    positions = [foundations.index(f"+{module}\n") for module in modules]
    assert positions == sorted(positions)
    assert foundations.index("lake env lean test/lean/DusartBoxLogFourth.lean") < positions[0]
    for test in ("XiReciprocalNorm", "DusartBoxCountingBudget"):
        assert positions[-1] < foundations.index(f"lake env lean test/lean/{test}.lean")


def test_two_cutoff_ci_build_order() -> None:
    root = Path(__file__).resolve().parents[2]
    workflow = (root / ".github/workflows/ci.yml").read_text()
    foundations = workflow.split("  lean-foundations:", 1)[1].split("  certificate-prebuild:", 1)[0]
    prefix = "PrimeFactorUnimodality.Helpers.Analytic"
    modules = (
        f"{prefix}.XiHeightBand",
        f"{prefix}.XiHeightBandGap",
        f"{prefix}.DusartBoxTwoCutoffs",
        f"{prefix}.DusartBoxTwoCutoffBudget",
        f"{prefix}.DusartBoxHeightGap",
        f"{prefix}.DusartBoxDampedHighTail",
    )
    positions = [foundations.index(f"+{module}\n") for module in modules]
    assert positions == sorted(positions)
    assert foundations.index("lake env lean test/lean/DusartBoxCountingBudget.lean") < positions[0]
    assert foundations.index(f"+{prefix}.ZetaZeroFreeInitial\n") < positions[1]
    for test in ("XiHeightBand", "DusartBoxTwoCutoffs"):
        assert positions[3] < foundations.index(f"lake env lean test/lean/{test}.lean")
    assert positions[-1] < foundations.index("lake env lean test/lean/DusartBoxHeightGap.lean")


def test_initial_bounded_gap_ci_build_order() -> None:
    root = Path(__file__).resolve().parents[2]
    workflow = (root / ".github/workflows/ci.yml").read_text()
    foundations = workflow.split("  lean-foundations:", 1)[1].split("  certificate-prebuild:", 1)[0]
    prefix = "PrimeFactorUnimodality.Helpers.Analytic"
    modules = (
        f"{prefix}.XiSmallHeightExclusion",
        f"{prefix}.ZetaZeroFreeBounded",
        f"{prefix}.KadiriInitialMaster",
        f"{prefix}.DusartBoxDampedTailBound",
        f"{prefix}.DusartBoxDampedBudget",
        f"{prefix}.DusartBoxInitialBudget",
        f"{prefix}.KadiriInitialLowGap",
    )
    positions = [foundations.index(f"+{module}\n") for module in modules]
    assert positions == sorted(positions)
    assert foundations.index("lake env lean test/lean/DusartBoxHeightGap.lean") < positions[3]
    assert foundations.index(f"+{prefix}.ZetaZeroFreeInitial\n") < positions[0]
    assert positions[2] < foundations.index("lake env lean test/lean/KadiriInitialMaster.lean")
    assert foundations.index(f"+{prefix}.KadiriBootstrapParameters\n") < positions[-1]
    for test in ("DusartBoxDampedBudget", "XiInitialBoundedGap"):
        assert positions[-1] < foundations.index(f"lake env lean test/lean/{test}.lean")


def test_rosser_window_ci_build_order() -> None:
    root = Path(__file__).resolve().parents[2]
    workflow = (root / ".github/workflows/ci.yml").read_text()
    foundations = workflow.split("  lean-foundations:", 1)[1].split("  certificate-prebuild:", 1)[0]
    prefix = "PrimeFactorUnimodality.Helpers.Analytic"
    candidate = "PrimeFactorUnimodality.Mathlib.Analysis.SpecialFunctions.Pow"
    modules = (
        f"{candidate}.LogDamped",
        f"{candidate}.LogDampedShape",
        f"{prefix}.XiWeightedCountingBounds",
        f"{prefix}.XiWeightedCountingPeak",
        f"{prefix}.XiRosserWindow",
        f"{prefix}.DusartBoxRosserWindow",
    )
    positions = [foundations.index(f"lake build \\\n            +{module}\n") for module in modules]
    assert positions == sorted(positions)
    assert foundations.index("lake env lean test/lean/XiInitialBoundedGap.lean") < positions[0]
    assert positions[1] < foundations.index("lake env lean test/lean/LogDampedPower.lean")
    assert foundations.index(f"+{prefix}.BacklundCountingHigh\n") < positions[2]
    assert foundations.index(f"+{prefix}.DusartBoxHeightGap\n") < positions[-1]
    for test in ("XiRosserWindow", "DusartBoxRosserWindow"):
        assert positions[-1] < foundations.index(f"lake env lean test/lean/{test}.lean")


def test_rosser_tail_ci_build_order() -> None:
    root = Path(__file__).resolve().parents[2]
    workflow = (root / ".github/workflows/ci.yml").read_text()
    foundations = workflow.split("  lean-foundations:", 1)[1].split("  certificate-prebuild:", 1)[0]
    prefix = "PrimeFactorUnimodality.Helpers.Analytic"
    candidate = "PrimeFactorUnimodality.Mathlib.Analysis.SpecialFunctions"
    modules = (
        f"{candidate}.Pow.LogDampedTail",
        f"{candidate}.Integrals.LogDamped",
        f"{prefix}.XiRosserAbel",
        f"{prefix}.XiRosserTailBound",
        f"{prefix}.XiRosserCutoff",
        f"{prefix}.XiRosserSymmetry",
        f"{prefix}.DusartBoxRosserTail",
        f"{prefix}.DusartBoxRosserBudget",
    )
    positions = [foundations.index(f"lake build \\\n            +{module}\n") for module in modules]
    assert positions == sorted(positions)
    assert foundations.index("lake env lean test/lean/DusartBoxRosserWindow.lean") < positions[0]
    assert positions[1] < foundations.index("lake env lean test/lean/LogDampedTail.lean")
    assert foundations.index(f"+{prefix}.XiZeroCountingImproper\n") < positions[2]
    assert foundations.index(f"+{prefix}.XiHeightTailEndpoint\n") < positions[4]
    for test in ("XiRosserTail", "DusartBoxRosserTail"):
        assert positions[-1] < foundations.index(f"lake env lean test/lean/{test}.lean")


def test_rosser_closed_bound_ci_build_order() -> None:
    root = Path(__file__).resolve().parents[2]
    workflow = (root / ".github/workflows/ci.yml").read_text()
    foundations = workflow.split("  lean-foundations:", 1)[1].split("  certificate-prebuild:", 1)[0]
    prefix = "PrimeFactorUnimodality.Helpers.Analytic"
    candidate = "PrimeFactorUnimodality.Mathlib.Analysis.SpecialFunctions"
    modules = (
        f"{candidate}.Pow.LogDampedMajorant",
        f"{candidate}.Integrals.LogPowerTail",
        f"{candidate}.Integrals.LogDampedBound",
        f"{prefix}.XiRosserClosedBounds",
        f"{prefix}.DusartBoxRosserClosedTail",
        f"{prefix}.DusartBoxRosserClosedBudget",
    )
    positions = [foundations.index(f"lake build \\\n            +{module}\n") for module in modules]
    assert positions == sorted(positions)
    assert foundations.index("lake env lean test/lean/DusartBoxRosserTail.lean") < positions[0]
    scalar_test = foundations.index("lake env lean test/lean/LogDampedClosedBound.lean")
    assert positions[2] < scalar_test < positions[3]
    assert positions[-1] < foundations.index(
        "lake env lean test/lean/DusartBoxRosserClosedBudget.lean"
    )
    assert positions[-1] < foundations.index(f"+{prefix}.ZetaExplicitBounds\n")


def test_rosser_increasing_band_ci_build_order() -> None:
    root = Path(__file__).resolve().parents[2]
    workflow = (root / ".github/workflows/ci.yml").read_text()
    foundations = workflow.split("  lean-foundations:", 1)[1].split("  certificate-prebuild:", 1)[0]
    prefix = "PrimeFactorUnimodality.Helpers.Analytic"
    candidate = "PrimeFactorUnimodality.Mathlib.Analysis.SpecialFunctions.Integrals"
    modules = (
        f"{candidate}.LogDampedWindow",
        f"{prefix}.XiRosserIncreasingBound",
        f"{prefix}.XiRosserIncreasingBand",
        f"{prefix}.DusartBoxRosserIncreasingBand",
        f"{prefix}.DusartBoxRosserBandBudget",
    )
    positions = [foundations.index(f"lake build \\\n            +{module}\n") for module in modules]
    assert positions == sorted(positions)
    assert (
        foundations.index("lake env lean test/lean/DusartBoxRosserClosedBudget.lean") < positions[0]
    )
    assert foundations.index(f"+{prefix}.XiHeightBand\n") < positions[2]
    candidate_test = foundations.index("lake env lean test/lean/LogDampedWindow.lean")
    assert positions[0] < candidate_test < positions[1]
    for test in ("XiRosserIncreasingBand", "DusartBoxRosserBandBudget"):
        assert positions[-1] < foundations.index(f"lake env lean test/lean/{test}.lean")


def test_rosser_nu_parameter_ci_build_order() -> None:
    root = Path(__file__).resolve().parents[2]
    workflow = (root / ".github/workflows/ci.yml").read_text()
    foundations = workflow.split("  lean-foundations:", 1)[1].split("  certificate-prebuild:", 1)[0]
    prefix = "PrimeFactorUnimodality.Helpers.Analytic"
    candidate = "PrimeFactorUnimodality.Mathlib.Analysis.SpecialFunctions.Integrals"
    modules = (
        f"{candidate}.LogDampedParameter",
        f"{prefix}.XiRosserNuTail",
        f"{prefix}.XiRosserNuWindow",
        f"{prefix}.DusartBoxRosserNuBudget",
    )
    positions = [foundations.index(f"lake build \\\n            +{module}\n") for module in modules]
    assert positions == sorted(positions)
    assert (
        foundations.index("lake env lean test/lean/DusartBoxRosserBandBudget.lean") < positions[0]
    )
    candidate_test = foundations.index("lake env lean test/lean/LogDampedParameter.lean")
    assert positions[0] < candidate_test < positions[1]
    for test in ("XiRosserNuBounds", "DusartBoxRosserNuBudget"):
        assert positions[-1] < foundations.index(f"lake env lean test/lean/{test}.lean")


def test_rosser_sharp_tail_ci_build_order() -> None:
    root = Path(__file__).resolve().parents[2]
    workflow = (root / ".github/workflows/ci.yml").read_text()
    foundations = workflow.split("  lean-foundations:", 1)[1].split("  certificate-prebuild:", 1)[0]
    prefix = "PrimeFactorUnimodality.Helpers.Analytic"
    candidate = "PrimeFactorUnimodality.Mathlib.Analysis.SpecialFunctions.Integrals"
    modules = (
        f"{candidate}.LogDampedSharpTail",
        f"{prefix}.XiRosserSharpTail",
        f"{prefix}.DusartBoxRosserSharpBudget",
    )
    previous = foundations.index("lake env lean test/lean/DusartBoxRosserNuBudget.lean")
    for module, test in zip(
        modules,
        ("LogDampedSharpTail", "XiRosserSharpTail", "DusartBoxRosserSharpBudget"),
        strict=True,
    ):
        build = foundations.index(f"lake build \\\n            +{module}\n")
        regression = foundations.index(f"lake env lean test/lean/{test}.lean")
        assert previous < build < regression
        previous = regression
    assert previous < foundations.index(f"+{prefix}.ZetaExplicitBounds\n")


def test_rosser_relative_step_ci_build_order() -> None:
    root = Path(__file__).resolve().parents[2]
    workflow = (root / ".github/workflows/ci.yml").read_text()
    foundations = workflow.split("  lean-foundations:", 1)[1].split("  certificate-prebuild:", 1)[0]
    prefix = "PrimeFactorUnimodality.Helpers.Analytic"
    modules = (
        "XiRosserSharpComparison",
        "DusartBoxRosserSharpBudget",
        "DusartBoxRosserRelative",
        "DusartBoxLogFourthStep",
    )
    previous = foundations.index("lake env lean test/lean/XiRosserSharpTail.lean")
    for module in modules:
        build = foundations.index(f"lake build \\\n            +{prefix}.{module}\n")
        regression = foundations.index(f"lake env lean test/lean/{module}.lean")
        assert previous < build < regression
        previous = regression
    assert previous < foundations.index(f"+{prefix}.ZetaExplicitBounds\n")


def test_main_ci_preserves_running_proof_build() -> None:
    root = Path(__file__).resolve().parents[2]
    workflow = (root / ".github/workflows/ci.yml").read_text()
    concurrency = workflow.split("concurrency:\n", 1)[1].split("\njobs:\n", 1)[0]
    assert "group: ${{ github.workflow }}-${{ github.ref }}" in concurrency
    assert "cancel-in-progress: ${{ github.ref != 'refs/heads/main' }}" in concurrency
