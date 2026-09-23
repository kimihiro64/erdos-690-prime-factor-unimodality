"""Keep region and zero-verification assemblers separate from numerical replay."""

from pathlib import Path

from scripts.lean_source import lean_imports, strip_lean_comments

ROOT = Path(__file__).resolve().parents[2]
ANALYTIC = "PrimeFactorUnimodality.Helpers.Analytic."
MODULES = (
    "MossinghoffTrudgianBounds",
    "KadiriEndpointRows",
    "KadiriInitialCutoff",
    "KadiriR6Parameters",
    "KadiriR6Gamma",
    "KadiriR6Tail",
    "KadiriR6Polynomial",
    "KadiriR6Correction",
    "KadiriR6Transform",
    "KadiriR6Bootstrap",
    "DusartSquaredBootstrap",
    "KadiriR6FourPoints",
    "XiCriticalLine",
    "XiSignRows",
    "XiZeroExhaustion",
    "XiMissingCount",
    "XiCompletedRows",
    "XiCountingIntegral",
    "XiIntegralVerification",
    "DusartZeroVerification",
    "TuringHorizontalLog",
    "TuringHorizontalShift",
    "TuringXiLogStep",
    "TuringXiLogBudget",
    "XiCanonicalLog",
    "XiLogRatio",
    "TuringXiLogInterchange",
    "TuringXiLogIntegral",
    "TuringGammaLower",
    "TuringZetaLogStep",
    "TuringHorizontalLower",
    "TuringPoleContour",
    "TuringCountPhase",
    "TuringCountIntegral",
    "TuringFiniteLogDerivative",
    "TuringHorizontalDerivative",
    "TuringLittlewoodReduction",
    "TuringHorizontalContinuity",
    "TuringLittlewood",
    "TuringPhaseBounds",
    "TuringCountingBudget",
    "XiTuringVerification",
    "DusartTuringVerification",
    "DusartReducedZeroVerification",
    "XiNormalizedCriticalLine",
    "XiEvaluationError",
    "XiStirlingPhase",
    "ZetaFiniteApproximation",
    "ZetaEulerTail",
    "ZetaEulerApproximation",
    "XiEulerEvaluation",
    "ZetaGroupedData",
    "ZetaGroupedEvaluation",
    "XiGroupedEvaluation",
    "ZetaGridData",
    "ZetaGridEvaluation",
    "XiGridEvaluation",
    "ThetaSquaredCheckpoints",
    "ThetaSquaredChain",
    "DusartCheckpointAnchors",
    "DusartCheckpointVerification",
)


def test_endpoint_assemblers_build_serially_before_scalar_replay() -> None:
    workflow = (ROOT / ".github/workflows/ci.yml").read_text()
    foundations = workflow.split("  lean-foundations:", 1)[1].split("  certificate-prebuild:", 1)[0]
    previous = foundations.index("lake env lean test/lean/KadiriElementaryBootstrap.lean")
    for module in MODULES:
        build = foundations.index(f"lake build \\\n            +{ANALYTIC}{module}\n")
        test = foundations.index(f"lake env lean test/lean/{module}.lean")
        assert previous < build < test
        previous = test
    integral_test = foundations.index("lake env lean test/lean/DusartZeroIntegralVerification.lean")
    assert foundations.index("lake env lean test/lean/DusartZeroVerification.lean") < integral_test
    previous_candidate = integral_test
    for leaf in ("HorizontalDecay", "RiemannZetaEulerDecay", "RiemannZetaLogIntegral"):
        candidate_build = foundations.index(
            f"+PrimeFactorUnimodality.Mathlib.NumberTheory.LSeries.{leaf}"
        )
        candidate_test = foundations.index(f"lake env lean test/lean/{leaf}.lean")
        assert previous_candidate < candidate_build < candidate_test
        previous_candidate = candidate_test
    assert previous_candidate < foundations.index(f"+{ANALYTIC}TuringHorizontalLog")
    previous_candidate = foundations.index("lake env lean test/lean/TuringHorizontalShift.lean")
    log_candidates = (
        ("SpecialFunctions.Integrals.LogShift", "LogShiftIntegral"),
        ("Complex.LogStep.Basic", "LogStepBasic"),
        ("Complex.LogStep.SmallHeight", "LogStepSmallHeight"),
        ("Complex.LogStep.LargeHeight", "LogStepLargeHeight"),
        ("Complex.LogStep.PairBound", "LogStepPairBound"),
    )
    for leaf, regression in log_candidates:
        candidate_build = foundations.index(f"+PrimeFactorUnimodality.Mathlib.Analysis.{leaf}")
        candidate_test = foundations.index(f"lake env lean test/lean/{regression}.lean")
        assert previous_candidate < candidate_build < candidate_test
        previous_candidate = candidate_test
    assert previous_candidate < foundations.index(f"+{ANALYTIC}TuringXiLogStep")
    previous_candidate = foundations.index("lake env lean test/lean/TuringHorizontalLower.lean")
    for leaf, regression in (
        ("SpecialFunctions.Complex.LogNormDeriv", "LogNormDeriv"),
        ("Calculus.ParametricIntervalIntegral", "ParametricRectangle"),
    ):
        candidate_build = foundations.index(f"+PrimeFactorUnimodality.Mathlib.Analysis.{leaf}")
        candidate_test = foundations.index(f"lake env lean test/lean/{regression}.lean")
        assert previous_candidate < candidate_build < candidate_test
        previous_candidate = candidate_test
    assert previous_candidate < foundations.index(f"+{ANALYTIC}TuringPoleContour")
    previous_candidate = foundations.index("lake env lean test/lean/TuringFiniteLogDerivative.lean")
    for leaf, regression in (
        ("NumberTheory.LSeries.RiemannZetaLogDerivDecay", "RiemannZetaLogDerivDecay"),
        ("NumberTheory.LSeries.RiemannZetaEulerIntegral", "RiemannZetaEulerIntegral"),
        ("NumberTheory.LSeries.RiemannZetaLogTailDerivative", "RiemannZetaLogTailDerivative"),
        ("MeasureTheory.Integral.IntervalIntegral.FiniteExceptions", "FiniteExceptions"),
        ("Analysis.Complex.Log.HorizontalContinuity", "LogHorizontalContinuity"),
        ("Analysis.Meromorphic.HorizontalFactorization", "MeromorphicHorizontalFactorization"),
        ("Analysis.Meromorphic.HorizontalContinuity", "MeromorphicHorizontalContinuity"),
        ("NumberTheory.LSeries.RiemannZetaLogContinuity", "RiemannZetaLogContinuity"),
    ):
        candidate_build = foundations.index(f"+PrimeFactorUnimodality.Mathlib.{leaf}")
        candidate_test = foundations.index(f"lake env lean test/lean/{regression}.lean")
        assert previous_candidate < candidate_build < candidate_test
        previous_candidate = candidate_test
    assert previous_candidate < foundations.index(f"+{ANALYTIC}TuringHorizontalDerivative\n")
    phase_candidate = foundations.index(
        "+PrimeFactorUnimodality.Mathlib.Analysis.SpecialFunctions.Complex.LogHeightBounds"
    )
    phase_candidate_test = foundations.index("lake env lean test/lean/LogHeightBounds.lean")
    assert foundations.index("lake env lean test/lean/TuringLittlewood.lean") < phase_candidate
    assert (
        phase_candidate < phase_candidate_test < foundations.index(f"+{ANALYTIC}TuringPhaseBounds")
    )
    candidate = foundations.index(
        "+PrimeFactorUnimodality.Mathlib.MeasureTheory.Integral.FinsetAbel"
    )
    assert candidate < foundations.index("lake env lean test/lean/FinsetAbel.lean")
    certificates = workflow.split("  certificate-prebuild:", 1)[1].split("  analytic-tail:", 1)[0]
    assert "KadiriKernelNumerical" not in foundations
    assert certificates.index(
        "+PrimeFactorUnimodality.Helpers.FiniteCertificates.KadiriKernelNumerical"
    ) < (certificates.index("lake env lean test/lean/KadiriKernelNumerical.lean"))


def test_endpoint_assembler_closure_has_no_scalar_replay_dependency() -> None:
    pending = [ANALYTIC + module for module in MODULES]
    visited: set[str] = set()
    while pending:
        module = pending.pop()
        if module in visited:
            continue
        visited.add(module)
        assert ".Generated." not in module
        assert ".FiniteCertificates." not in module
        assert not module.startswith("LeanCert.")
        path = ROOT.joinpath(*module.split(".")).with_suffix(".lean")
        if path.is_file():
            pending.extend(lean_imports(strip_lean_comments(path.read_text())))


def test_moderate_lehman_domain_reaches_endpoint_rows() -> None:
    workflow = (ROOT / ".github/workflows/ci.yml").read_text()
    assert workflow.index(f"+{ANALYTIC}XiLehmanLogBound\n") < workflow.index(
        f"+{ANALYTIC}XiLehmanBudget\n"
    )
    assert (
        workflow.index(f"+{ANALYTIC}XiLehmanAffine\n")
        < workflow.index("lake env lean test/lean/XiLehmanLogBound.lean")
        < workflow.index(f"+{ANALYTIC}KadiriTailEnvelope\n")
    )
    for module in (
        "KadiriLehmanMaster",
        "KadiriExplicitMaster",
        "KadiriRegionMaster",
        "KadiriBootstrapMaster",
        "KadiriUniformBootstrap",
        "KadiriSplitBootstrap",
        "KadiriScaleCoverBootstrap",
        "KadiriGridBootstrap",
        "KadiriConservativeBootstrap",
        "KadiriElementaryBootstrap",
        "KadiriEndpointRows",
    ):
        path = ROOT / "PrimeFactorUnimodality/Helpers/Analytic" / f"{module}.lean"
        source = strip_lean_comments(path.read_text())
        assert "10 ^ 9" not in source
        assert "1000000000" not in source
    budget = ROOT / "PrimeFactorUnimodality/Helpers/Analytic/XiLehmanBudget.lean"
    assert "else xiLehmanLogBound |t| H" in strip_lean_comments(budget.read_text())


def test_turing_consumers_do_not_assume_counting_error() -> None:
    for module in (
        "XiTuringVerification",
        "DusartTuringVerification",
        "DusartReducedZeroVerification",
    ):
        path = ROOT / "PrimeFactorUnimodality/Helpers/Analytic" / f"{module}.lean"
        source = strip_lean_comments(path.read_text())
        assert "(herror :" not in source
        assert "(hcount :" not in source
        assert "(hlow :" not in source
        assert "turingCountErrorBudget" in source


def test_reduced_psi_cutoff_is_connected_before_legacy_consumers() -> None:
    workflow = (ROOT / ".github/workflows/ci.yml").read_text()
    ordered = (
        "XiPositiveReciprocalMass",
        "XiLowReciprocalNormBound",
        "XiZeroNumericalBounds",
        "XiReducedCutoffBounds",
        "DusartEndpointElementary",
        "DusartReducedPsiEndpoint",
        "DusartPsiEndpoint",
        "DusartThetaSquaredEndpoint",
        "XiTuringVerification",
        "DusartReducedZeroVerification",
    )
    positions = [workflow.index(f"+{ANALYTIC}{module}\n") for module in ordered]
    assert positions == sorted(positions)
    root = ROOT / "PrimeFactorUnimodality/Helpers/Analytic"
    reduced = strip_lean_comments((root / "DusartReducedPsiEndpoint.lean").read_text())
    assert "xiLowHeightIndices 25000000" in reduced
    assert "xiLowHeightIndices 1000000000" not in reduced
    assert "dusartBoxPowerPsiBound 2 (1 / 600000) x₀ 25 1250000 25000000" in reduced
    legacy = strip_lean_comments((root / "DusartPsiEndpoint.lean").read_text())
    assert "apply abs_psi_sub_div_lt_of_reduced_low_gap hx" in legacy
    for module in (
        "XiPositiveReciprocalMass",
        "XiReducedCutoffBounds",
        "DusartEndpointElementary",
        "DusartReducedPsiEndpoint",
        "DusartReducedZeroVerification",
    ):
        assert f"lake env lean test/lean/{module}.lean" in workflow


def test_reduced_region_reuses_one_height_uniform_chain() -> None:
    root = ROOT / "PrimeFactorUnimodality/Helpers/Analytic"
    for module in (
        "KadiriR6Parameters",
        "KadiriR6Gamma",
        "KadiriR6Tail",
        "KadiriR6Correction",
    ):
        source = strip_lean_comments((root / f"{module}.lean").read_text())
        assert "(hT : 25000000 ≤ T)" in source
        assert "1000000000" not in source
    parameters = strip_lean_comments((root / "KadiriR6Parameters.lean").read_text())
    assert "437 / 1000" in parameters
    assert "98 / 10000" in parameters
    assert "9922 / 10000" in parameters
    chain = strip_lean_comments((root / "KadiriR6FourPoints.lean").read_text())
    assert chain.count("kadiriSix_chain_of_four_points_from (by norm_num)") == 2
    assert "25000000 69 6" in chain
    assert "1000000000 56 6" in chain
    consumer = strip_lean_comments((root / "DusartReducedZeroVerification.lean").read_text())
    assert "kadiriHighRegion_six_of_reduced_rows_and_four_points" in consumer
    assert "(kadiriSix_reduced_chain_of_four_points hg hm hd he hpoints)" in consumer


def test_xi_evaluator_candidates_are_checked_before_consumers() -> None:
    workflow = (ROOT / ".github/workflows/ci.yml").read_text()
    foundations = workflow.split("  lean-foundations:", 1)[1].split("  certificate-prebuild:", 1)[0]
    previous = foundations.index("lake env lean test/lean/DusartTuringVerification.lean")
    candidates = [
        ("Analysis.SpecialFunctions.Complex.RotationError", "RotationError"),
        *[
            (f"NumberTheory.BernoulliPeriodic.{leaf}", f"Bernoulli{leaf}")
            for leaf in ("Normalized", "Integrability", "Cells", "Recursion", "ExplicitBound")
        ],
    ]
    for module, regression in candidates:
        build = foundations.index(f"+PrimeFactorUnimodality.Mathlib.{module}\n")
        test = foundations.index(f"lake env lean test/lean/{regression}.lean")
        assert previous < build < test
        previous = test
    assert previous < foundations.index(f"+{ANALYTIC}XiNormalizedCriticalLine\n")


def test_xi_evaluator_does_not_assume_a_zero_or_rh() -> None:
    for module in (
        "ZetaFiniteApproximation",
        "ZetaEulerTail",
        "ZetaEulerApproximation",
        "XiEulerEvaluation",
        "ZetaGroupedData",
        "ZetaGroupedEvaluation",
        "XiGroupedEvaluation",
        "ZetaGridData",
        "ZetaGridEvaluation",
        "XiGridEvaluation",
        "RadixTwiddleChecks",
        "CheckedZetaGrid",
    ):
        path = ROOT.joinpath(*(ANALYTIC + module).split(".")).with_suffix(".lean")
        source = strip_lean_comments(path.read_text())
        assert "RiemannHypothesis" not in source
        assert "IsNontrivialZero" not in source
    source = strip_lean_comments(
        (ROOT / "PrimeFactorUnimodality/Helpers/Analytic/ZetaEulerApproximation.lean").read_text()
    )
    assert "riemannZeta_sub_eulerApproxOrder" in source
    assert "zetaEulerTail_recursion" in source
    assert "norm_zetaEulerTail_le" in source


def test_grouped_evaluator_is_checked_before_its_actual_sign_consumer() -> None:
    workflow = (ROOT / ".github/workflows/ci.yml").read_text()
    previous = workflow.index("lake env lean test/lean/XiEulerEvaluation.lean")
    for module, regression in (
        ("Analysis.SpecialFunctions.Complex.ExponentialMoments", "ExponentialMoments"),
        ("Analysis.SpecialFunctions.Complex.GroupedExponential", "GroupedExponential"),
        ("Analysis.SpecialFunctions.Complex.GroupedRounding", "GroupedRounding"),
        ("NumberTheory.LSeries.GroupedEvaluation", "GroupedDirichlet"),
    ):
        build = workflow.index(f"+PrimeFactorUnimodality.Mathlib.{module}\n")
        test = workflow.index(f"lake env lean test/lean/{regression}.lean")
        assert previous < build < test
        previous = test
    for module in ("ZetaGroupedData", "ZetaGroupedEvaluation", "XiGroupedEvaluation"):
        build = workflow.index(f"+{ANALYTIC}{module}\n")
        test = workflow.index(f"lake env lean test/lean/{module}.lean")
        assert previous < build < test
        previous = test
    root = ROOT / "PrimeFactorUnimodality/Helpers/Analytic"
    bound = strip_lean_comments((root / "ZetaGroupedEvaluation.lean").read_text())
    assert "norm_dirichlet_sum_sub_rounded_with_centers_le" in bound
    assert "norm_riemannZeta_sub_eulerApproxOrder_le" in bound
    signs = strip_lean_comments((root / "XiGroupedEvaluation.lean").read_text())
    assert "XiSignRow.valid_of_grouped_endpoints" in signs
    assert "hp.norm_zeta_sub_value_le hd" in signs


def test_radix_grid_has_shared_arrays_and_sequential_checked_consumers() -> None:
    workflow = (ROOT / ".github/workflows/ci.yml").read_text()
    previous = workflow.index("lake env lean test/lean/XiGroupedEvaluation.lean")
    for module, regression in (
        ("Mathlib.Analysis.Fourier.RadixTwo", "RadixTwo"),
        ("Mathlib.Analysis.Fourier.IntegerGrid", "IntegerGrid"),
        ("Mathlib.Analysis.Fourier.RadixError", "RadixError"),
        ("Mathlib.Data.Vector.ScatterAdd", "ScatterAdd"),
        ("Mathlib.Analysis.Fourier.GroupedGrid", "GroupedGrid"),
        ("Helpers.Analytic.ZetaGridData", "ZetaGridData"),
        ("Helpers.Analytic.ZetaGridEvaluation", "ZetaGridEvaluation"),
        ("Helpers.Analytic.XiGridEvaluation", "XiGridEvaluation"),
    ):
        build = workflow.index(f"+PrimeFactorUnimodality.{module}\n")
        test = workflow.index(f"lake env lean test/lean/{regression}.lean")
        assert previous < build < test
        previous = test
    root = ROOT / "PrimeFactorUnimodality"
    radix = strip_lean_comments((root / "Mathlib/Analysis/Fourier/RadixTwo.lean").read_text())
    assert "let u := radixTwo" in radix
    assert "let v := radixTwo" in radix
    assert "let powers := powerTable" in radix
    grouped = strip_lean_comments((root / "Mathlib/Analysis/Fourier/GroupedGrid.lean").read_text())
    assert ").scatterAdd (B.toList.map" in grouped
    bound = strip_lean_comments((root / "Helpers/Analytic/ZetaGridEvaluation.lean").read_text())
    assert "norm_exp_polynomial_grid_sub_traces_le" in bound
    assert "hp.asGrouped.norm_zeta_sub_value_le hd.1" in bound
    signs = strip_lean_comments((root / "Helpers/Analytic/XiGridEvaluation.lean").read_text())
    assert "XiSignRow.valid_of_grid_endpoints" in signs
    assert "hp.norm_zeta_sub_value_le hd" in signs


def test_rational_grid_checks_discharge_actual_fourier_premises() -> None:
    workflow = (ROOT / ".github/workflows/ci.yml").read_text()
    previous = workflow.index("lake env lean test/lean/XiGridEvaluation.lean")
    for module, regression in (
        ("Mathlib.Analysis.Complex.RationalPoint", "RationalPoint"),
        ("Mathlib.Analysis.Fourier.RadixRoot", "RadixRoot"),
        ("Mathlib.Analysis.Fourier.RationalTrace", "RationalTrace"),
        ("Mathlib.Analysis.Fourier.RationalAlias", "RationalAlias"),
        ("Helpers.Analytic.RadixTwiddleChecks", "RadixTwiddleChecks"),
        ("Helpers.Analytic.CheckedZetaGrid", "CheckedZetaGrid"),
    ):
        build = workflow.index(f"+PrimeFactorUnimodality.{module}\n")
        test = workflow.index(f"lake env lean test/lean/{regression}.lean")
        assert previous < build < test
        previous = test
    root = ROOT / "PrimeFactorUnimodality"
    alias = strip_lean_comments((root / "Mathlib/Analysis/Fourier/RationalAlias.lean").read_text())
    assert "rows.map" in alias
    assert ".toList" not in alias
    phase = strip_lean_comments((root / "Helpers/Analytic/RadixTwiddleChecks.lean").read_text())
    assert "mem_cosComputable" in phase
    assert "mem_sinComputable" in phase
    assert "ComputableReduced" not in phase
    consumer = strip_lean_comments((root / "Helpers/Analytic/CheckedZetaGrid.lean").read_text())
    assert "r.groups.Nodup" in consumer
    assert "checkTwiddleTables_sound" in consumer
    assert "rationalAliasVector_map" in consumer
    assert "hp.norm_zeta_sub_value_le (r.valid_of_check" in consumer


def test_optional_rational_checkers_do_not_import_replay_or_tactic_modules() -> None:
    pending = [ANALYTIC + name for name in ("RadixTwiddleChecks", "CheckedZetaGrid")]
    visited: set[str] = set()
    while pending:
        module = pending.pop()
        if module in visited:
            continue
        visited.add(module)
        assert ".Generated." not in module
        assert ".FiniteCertificates." not in module
        if module.startswith("LeanCert."):
            assert module == "LeanCert.Core.IntervalRat.Taylor"
            continue
        if not module.startswith("PrimeFactorUnimodality."):
            continue
        path = ROOT.joinpath(*module.split(".")).with_suffix(".lean")
        source = strip_lean_comments(path.read_text())
        pending.extend(lean_imports(source))


def test_theta_checkpoint_consumers_derive_band_and_anchor_obligations() -> None:
    source = strip_lean_comments(
        (
            ROOT / "PrimeFactorUnimodality/Helpers/Analytic/DusartCheckpointVerification.lean"
        ).read_text()
    )
    assert "thetaLogSquared_on_published_band_of_checkpoints" in source
    assert "hsteps.bound" in source
    assert "hasThetaLogSquaredError_of_lower_band_and_turing_rows" in source
    assert "ThetaSquaredCheckpoint.lower_anchor" in source
    assert "ThetaSquaredCheckpoint.upper_anchor" in source
    assert "(finite : ∀" not in source
    assert "(lowerAnchor :" not in source
    assert "(upperAnchor :" not in source
