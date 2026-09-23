"""Keep sieve-count semantics local, checked and outside numerical replay jobs."""

from pathlib import Path

from scripts.lean_source import strip_lean_comments

ROOT = Path(__file__).resolve().parents[2]
BASE = "PrimeFactorUnimodality."


def test_sieve_count_foundations_build_serially() -> None:
    workflow = (ROOT / ".github/workflows/ci.yml").read_text()
    foundations = workflow.split("  lean-foundations:", 1)[1].split("  certificate-prebuild:", 1)[0]
    previous = foundations.index("lake env lean test/lean/DusartCheckedThetaTrace.lean")
    pairs = (
        (BASE + "Mathlib.Data.Nat.BitCount", "BitCount"),
        ("PrimeCert.Pocklington", "PrimeCertCompatibility"),
        (BASE + "Helpers.Arithmetic.SievePrimeCounting", "SievePrimeCounting"),
        (BASE + "Helpers.Arithmetic.SievePrimeCountIncrements", "SievePrimeCountIncrements"),
        (BASE + "Helpers.Analytic.SievedThetaPrimeTrace", "SievedThetaPrimeTrace"),
    )
    for module, test in pairs:
        build = foundations.index(f"+{module}\n")
        regression = foundations.index(f"lake env lean test/lean/{test}.lean")
        assert previous < build < regression
        previous = regression
    assert (
        foundations.index("scripts/patch_primecert_compat.py")
        < foundations.index("+PrimeCert.SieveCorrect\n")
        < foundations.index("+PrimeCert.Pocklington\n")
    )


def test_adjacent_counts_do_not_recount_the_prefix() -> None:
    arithmetic = ROOT / "PrimeFactorUnimodality/Helpers/Arithmetic"
    source = strip_lean_comments((arithmetic / "SievePrimeCountIncrements.lean").read_text())
    checker = source.split("def checkSieveCountStep", 1)[1].split("theorem", 1)[0]
    assert "sievePrimeCount " not in checker
    assert "Nat.bitCountBlock k bits (wheelLength a)" in checker
    assert "wheelLength b - wheelLength a ≤ 2 ^ k" in checker
    assert "3 ≤ a ∧ a ≤ b ∧ b ≤ N" in checker
    adapter = ROOT / "PrimeFactorUnimodality/Helpers/Analytic/SievedThetaPrimeTrace.lean"
    source = strip_lean_comments(adapter.read_text())
    assert "checkSieveCountStep N k bits start.point start.count next.point next.count" in source
    assert "counts_of_sieve_checks h hs.2.1 hcounts" in source
    assert "1441000000000 ≤ q.point" in source
