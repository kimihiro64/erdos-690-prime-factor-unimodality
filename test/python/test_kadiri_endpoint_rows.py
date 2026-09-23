"""Keep the bootstrap assembler separate from its small scalar replay rows."""

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
