"""Keep the direct log-square Dusart route serial and independent of replays."""

from __future__ import annotations

from pathlib import Path

from scripts.lean_source import lean_imports, strip_lean_comments

ROOT = Path(__file__).resolve().parents[2]
MODULES = (
    "ThetaLogSquaredError",
    "DusartTwoTermComparison",
    "DusartShortIntervalSquared",
    "DusartPrimeCountingSquared",
    "DusartSquaredAtPublishedCutoff",
    "DusartThetaSquaredEndpoint",
)


def test_log_square_modules_build_serially_in_foundations() -> None:
    workflow = (ROOT / ".github/workflows/ci.yml").read_text()
    foundations = workflow.split("  lean-foundations:", 1)[1].split("  certificate-prebuild:", 1)[0]
    previous = foundations.index("lake env lean test/lean/DusartLogarithmicTheta.lean")
    for module in MODULES:
        build = foundations.index(
            f"lake build \\\n            +PrimeFactorUnimodality.Helpers.Analytic.{module}\n"
        )
        test = foundations.index(f"lake env lean test/lean/{module}.lean")
        assert previous < build < test
        previous = test
    assert previous < foundations.index(
        "+PrimeFactorUnimodality.Helpers.Analytic.ZetaExplicitBounds\n"
    )


def test_log_square_route_has_no_finite_replay_dependency() -> None:
    pending = [f"PrimeFactorUnimodality.Helpers.Analytic.{module}" for module in MODULES]
    visited: set[str] = set()
    while pending:
        module = pending.pop()
        if module in visited:
            continue
        visited.add(module)
        assert ".Generated." not in module
        assert ".FiniteCertificates." not in module
        path = ROOT.joinpath(*module.split(".")).with_suffix(".lean")
        if path.is_file():
            pending.extend(lean_imports(strip_lean_comments(path.read_text())))
