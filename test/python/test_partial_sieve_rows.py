"""Keep exact counting identities and external-row checks in the serial foundations job."""

from pathlib import Path

from scripts.lean_source import strip_lean_comments

ROOT = Path(__file__).resolve().parents[2]
BASE = "PrimeFactorUnimodality."


def test_partial_sieve_foundations_build_serially() -> None:
    workflow = (ROOT / ".github/workflows/ci.yml").read_text()
    foundations = workflow.split("  lean-foundations:", 1)[1].split("  certificate-prebuild:", 1)[0]
    previous = foundations.index("lake env lean test/lean/SievedThetaPrimeTrace.lean")
    for name, directory in (
        ("PartialSieve", "Mathlib.NumberTheory"),
        ("PartialSievePrimeLeaves", "Mathlib.NumberTheory"),
        ("PrimeCountingMeissel", "Mathlib.NumberTheory"),
        ("PartialSieveRows", "Helpers.Arithmetic"),
        ("MeisselRows", "Helpers.Arithmetic"),
    ):
        build = foundations.index(f"+{BASE}{directory}.{name}\n")
        test = foundations.index(f"lake env lean test/lean/{name}.lean")
        assert previous < build < test
        previous = test


def test_local_checks_do_not_recompute_partial_sieve() -> None:
    path = ROOT / "PrimeFactorUnimodality/Helpers/Arithmetic/PartialSieveRows.lean"
    source = strip_lean_comments(path.read_text())
    checker = source.split("def checkPartialSieveRow", 1)[1].split("theorem", 1)[0]
    assert "sievePhi" not in checker
    assert "l < i ∧ h < i" in checker
    assert "k < knownSize" in checker
    assert "right.point = r.point / p left.level" in checker
    assert "r.value + right.value = left.value" in checker
    assembler = source.split("theorem partialSieveRows_valid", 1)[1]
    assert "hknown : ∀ k < knownSize, (known k).Valid p" in assembler


def test_meissel_requires_actual_counts_and_local_sum_checks() -> None:
    path = ROOT / "PrimeFactorUnimodality/Helpers/Arithmetic/MeisselRows.lean"
    source = strip_lean_comments(path.read_text())
    assert "Nat.primeCounting (n / p i) = (rows i).count" in source
    assert "p i = Nat.nth Nat.Prime i" in source
    assert "meisselQuotientRows_sum hab hstart hsteps" in source
    assert "n < p b ^ 2 ∧ n < p a ^ 3" in source
    assert "count + total + 1 = phi + b" in source
