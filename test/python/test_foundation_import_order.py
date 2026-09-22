"""Reject foundation tests that rely on artifacts absent from a clean CI build."""

from functools import cache
from pathlib import Path

from scripts.lean_source import lean_imports, strip_lean_comments


def missing_test_imports(root: Path, commands: str) -> list[str]:
    """Follow owned transitive imports of each explicit build, then check tests."""

    @cache
    def closure(module: str) -> frozenset[str]:
        if not module.startswith("PrimeFactorUnimodality."):
            return frozenset()
        source = root / (module.replace(".", "/") + ".lean")
        imports = lean_imports(strip_lean_comments(source.read_text()))
        return frozenset({module}).union(*(closure(dependency) for dependency in imports))

    available: set[str] = set()
    missing: list[str] = []
    for line in commands.splitlines():
        command = line.strip()
        if command.startswith("+"):
            for target in command.split():
                if target.startswith("+"):
                    available.update(closure(target[1:]))
        elif command.startswith("lake env lean test/lean/"):
            test = command.split()[3]
            imports = lean_imports(strip_lean_comments((root / test).read_text()))
            for dependency in imports:
                for module in sorted(closure(dependency) - available):
                    missing.append(f"{test}: {module}")
    return missing


def test_every_foundation_test_import_is_built_first() -> None:
    root = Path(__file__).resolve().parents[2]
    workflow = (root / ".github/workflows/ci.yml").read_text()
    foundations = workflow.split("  lean-foundations:", 1)[1].split("  certificate-prebuild:", 1)[0]
    assert not (missing := missing_test_imports(root, foundations)), "\n".join(missing)


def test_unbuilt_gamma_budget_is_detected() -> None:
    root = Path(__file__).resolve().parents[2]
    commands = (
        "+PrimeFactorUnimodality.Helpers.Analytic.SmoothedGammaFactorBounds\n"
        "lake env lean test/lean/KadiriGammaRealBounds.lean\n"
    )
    assert missing_test_imports(root, commands) == [
        "test/lean/KadiriGammaRealBounds.lean: "
        "PrimeFactorUnimodality.Helpers.Analytic.KadiriGammaBudget"
    ]
