"""Guard compact prime-count transport and its independent lower-band checks."""

from pathlib import Path

from scripts.lean_source import strip_lean_comments

ROOT = Path(__file__).resolve().parents[2]
BASE = "PrimeFactorUnimodality."


def test_theta_prime_checks_build_serially_before_replay() -> None:
    workflow = (ROOT / ".github/workflows/ci.yml").read_text()
    foundations = workflow.split("  lean-foundations:", 1)[1].split("  certificate-prebuild:", 1)[0]
    previous = foundations.index("lake env lean test/lean/DusartCheckpointVerification.lean")
    modules = (
        ("Mathlib.NumberTheory.Chebyshev.Intervals", "ChebyshevIntervals"),
        ("Helpers.Analytic.ThetaPrimeCheckpoints", "ThetaPrimeCheckpoints"),
        ("Helpers.Analytic.CheckedThetaPrimeTrace", "CheckedThetaPrimeTrace"),
        ("Helpers.Analytic.ThetaSquaredChecks", "ThetaSquaredChecks"),
        ("Helpers.Analytic.DusartCheckedThetaTrace", "DusartCheckedThetaTrace"),
    )
    for module, test in modules:
        build = foundations.index(f"+{BASE}{module}\n")
        regression = foundations.index(f"lake env lean test/lean/{test}.lean")
        assert previous < build < regression
        previous = regression


def test_theta_trace_retains_exact_counts_and_final_endpoint_checks() -> None:
    analytic = ROOT / "PrimeFactorUnimodality/Helpers/Analytic"
    trace = strip_lean_comments((analytic / "CheckedThetaPrimeTrace.lean").read_text())
    assert "Nat.primeCounting s.point = s.count" in trace
    assert "intervalSubset (c.log s.point) s.log" in trace
    assert "start.checkStep next && checkLog c next" in trace
    assert "checkTrace_append" in trace
    coverage = strip_lean_comments((analytic / "ThetaSquaredChecks.lean").read_text())
    for field in ("point", "lower", "upper", "logUpper"):
        assert f"p.{field} = q.{field}" in coverage
    assert "Step c p next" in coverage
    consumer = strip_lean_comments((analytic / "DusartCheckedThetaTrace.lean").read_text())
    assert "Chebyshev.theta" in consumer
    assert "1441000000000 ≤ q.point" in consumer
    assert "p.point ≤ 3594641" in consumer
    assert "chain_of_checkFrom" in consumer
    assert "(hpoints :" not in consumer
