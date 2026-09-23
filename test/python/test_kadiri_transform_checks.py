"""Keep checked R6 expressions separate from their four numerical replay rows."""

from pathlib import Path

from scripts.lean_source import lean_imports, strip_lean_comments

ROOT = Path(__file__).resolve().parents[2]
BASE = "PrimeFactorUnimodality.Helpers."


def test_transform_checks_build_before_numerical_rows() -> None:
    workflow = (ROOT / ".github/workflows/ci.yml").read_text()
    foundations = workflow.split("  lean-foundations:", 1)[1].split("  certificate-prebuild:", 1)[0]
    certificates = workflow.split("  certificate-prebuild:", 1)[1].split("  analytic-tail:", 1)[0]
    previous = foundations.index("lake env lean test/lean/KadiriR6FourPoints.lean")
    for module in ("ExpIntegralExpressions", "KadiriTransformExpressions", "KadiriTransformChecks"):
        build = foundations.index(f"+{BASE}Analytic.{module}\n")
        test = foundations.index(f"lake env lean test/lean/{module}.lean")
        assert previous < build < test
        previous = test
    previous = certificates.index("lake env lean test/lean/KadiriKernelNumerical.lean")
    for module in ("KadiriTransformNumerical", "DusartVerifiedBootstrap"):
        assert module not in foundations
        build = certificates.index(f"+{BASE}FiniteCertificates.{module}\n")
        test = certificates.index(f"lake env lean test/lean/{module}.lean")
        assert previous < build < test
        previous = test


def test_transform_numerics_reuse_the_existing_rows_and_kernel_bounds() -> None:
    module = (
        ROOT / "PrimeFactorUnimodality/Helpers/FiniteCertificates/KadiriTransformNumerical.lean"
    )
    source = strip_lean_comments(module.read_text())
    assert BASE + "FiniteCertificates.KadiriKernelNumerical" in lean_imports(source)
    assert "∀ i : Fin 4, checkKadiriSixTransformRow i (-40) 16 = true" in source
    assert source.count("decide +kernel") == 1
    assert "kadiriSixTransformBounds_of_checks" in source
    assert "checkLowerBoundDyadic" not in source
    checks = ROOT / "PrimeFactorUnimodality/Helpers/Analytic/KadiriTransformChecks.lean"
    semantics = strip_lean_comments(checks.read_text())
    assert "checkLowerBoundDyadicChecked" in semantics
    assert "verify_lower_bound_dyadic_checked" in semantics
    assert "KadiriTransformExpressions.gap_eval" in semantics
    assert "(kadiriSixTransformRow i).1 (kadiriSixTransformRow i).2" in semantics


def test_verified_consumers_do_not_assume_the_bootstrap_or_weaken_the_cutoff() -> None:
    module = ROOT / "PrimeFactorUnimodality/Helpers/FiniteCertificates/DusartVerifiedBootstrap.lean"
    source = strip_lean_comments(module.read_text())
    assert "(hchain :" not in source
    assert "(hpoints : KadiriSixTransformBounds)" not in source
    theta_ray = source.split("theorem hasThetaLogSquaredError_above_endpoint_of_verified_low", 1)[1]
    theta_ray = theta_ray.split("theorem", 1)[0]
    assert "xiLowHeightIndices 1000000000" in theta_ray
    assert "25000000" not in theta_ray
    assert "kadiriSix_endpoint_chain hlow" in theta_ray
