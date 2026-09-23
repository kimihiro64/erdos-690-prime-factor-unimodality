"""Keep region and zero-verification assemblers separate from numerical replay."""

from pathlib import Path

from scripts.lean_source import lean_imports, strip_lean_comments

ROOT = Path(__file__).resolve().parents[2]
ANALYTIC = "PrimeFactorUnimodality.Helpers.Analytic."
MODULES = (
    "MossinghoffTrudgianBounds",
    "KadiriEndpointRows",
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
