"""Keep the reduced finite obligation connected to the original global theta bound."""

from pathlib import Path

from scripts.lean_source import strip_lean_comments

ROOT = Path(__file__).resolve().parents[2]
ANALYTIC = ROOT / "PrimeFactorUnimodality/Helpers/Analytic"
VERIFIED = ROOT / "PrimeFactorUnimodality/Helpers/FiniteCertificates/DusartVerifiedBootstrap.lean"


def theorem(source: str, name: str) -> str:
    """Select one named theorem, ignoring documentation."""
    return strip_lean_comments(source).split(f"theorem {name}", 1)[1].split("theorem", 1)[0]


def test_earlier_modules_and_tests_are_serial_foundations() -> None:
    workflow = (ROOT / ".github/workflows/ci.yml").read_text()
    foundations = workflow.split("  lean-foundations:", 1)[1].split("  certificate-prebuild:", 1)[0]
    previous = foundations.index("lake env lean test/lean/DusartReducedPsiEndpoint.lean")
    for suffix in ("Scalars", "Budget", "Theta", ""):
        module = "DusartEarlierCutoff" + suffix
        build = foundations.index(f"+PrimeFactorUnimodality.Helpers.Analytic.{module}\n")
        test = foundations.index(f"lake env lean test/lean/{module}.lean")
        assert previous < build < test
        previous = test
    assert foundations.index("lake env lean test/lean/DusartSquaredAnalyticRay.lean") < previous


def test_actual_consumers_need_only_the_shorter_band() -> None:
    source = VERIFIED.read_text()
    lower = theorem(source, "hasThetaLogSquaredError_of_lower_band_and_verified_low")
    assert "x ≤ 10000000000" in lower
    assert "1441000000000" not in lower
    assert "HasThetaLogSquaredError (1 / 5) 3594641" in lower
    assert "xiLowHeightIndices 1000000000" in lower
    assert "hasThetaLogSquaredError_of_earlier_band_and_zero_data" in lower
    for name in (
        "hasThetaLogSquaredError_of_early_prime_trace_and_verified_low",
        "hasThetaLogSquaredError_of_verified_checkpoints_and_turing_rows",
    ):
        consumer = theorem(source, name)
        assert "10000000000 ≤ q.point" in consumer
        assert "1441000000000" not in consumer
        assert "HasThetaLogSquaredError (1 / 5) 3594641" in consumer
        assert "hasThetaLogSquaredError_of_lower_band_and_verified_low" in consumer


def test_bridge_retains_both_intervals_and_original_infinite_ray() -> None:
    source = (ANALYTIC / "DusartEarlierCutoffTheta.lean").read_text()
    bridge = theorem(source, "abs_theta_sub_le_logSquared_early_bridge")
    assert "(hx : (10000000000 :" in bridge
    assert "x ≤ 1441000000000" in bridge
    assert "by_cases h : x ≤ 100000000000" in bridge
    assert "abs_theta_sub_le_logSquared_early_first hx h hgap" in bridge
    assert "abs_theta_sub_le_logSquared_early_second (le_of_not_ge h) hX hgap" in bridge
    source = (ANALYTIC / "DusartEarlierCutoff.lean").read_text()
    ray = theorem(source, "hasThetaLogSquaredError_above_earlier_cutoff")
    assert "xiLowHeightIndices 1000000000" in ray
    assert "(hreg :" in ray
    assert "hasThetaLogSquaredError_above_endpoint hgap hreg" in ray
    assert "dusartEarlier_low_zero_restriction hgap" in ray
