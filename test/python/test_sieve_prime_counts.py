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
        (BASE + "Mathlib.Data.Nat.BitCountPacked", "BitCountPacked"),
        ("PrimeCert.Pocklington", "PrimeCertCompatibility"),
        (BASE + "Helpers.Arithmetic.SievePrimeCounting", "SievePrimeCounting"),
        (BASE + "Helpers.Arithmetic.SievePrimeCountIncrements", "SievePrimeCountIncrements"),
        (BASE + "Helpers.Analytic.SievedThetaPrimeTrace", "SievedThetaPrimeTrace"),
        (BASE + "Mathlib.Data.Nat.BitProduct", "BitProduct"),
        (BASE + "Helpers.Arithmetic.SievePrimeProduct", "SievePrimeProduct"),
        (BASE + "Helpers.Analytic.NaturalLogScaling", "NaturalLogScaling"),
        (BASE + "Helpers.Analytic.SievedThetaAnchor", "SievedThetaAnchor"),
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
    assert "Nat.bitCountBlockPacked k bits (wheelLength a)" in checker
    assert "wheelLength b - wheelLength a ≤ 2 ^ k" in checker
    assert "3 ≤ a ∧ a ≤ b ∧ b ≤ N" in checker
    adapter = ROOT / "PrimeFactorUnimodality/Helpers/Analytic/SievedThetaPrimeTrace.lean"
    source = strip_lean_comments(adapter.read_text())
    assert "checkSieveCountStep N k bits start.point start.count next.point next.count" in source
    assert "counts_of_sieve_checks h hs.2.1 hcounts" in source
    assert "1441000000000 ≤ q.point" in source


def test_prime_count_checkers_use_proved_packed_backend() -> None:
    arithmetic = ROOT / "PrimeFactorUnimodality/Helpers/Arithmetic"
    source = strip_lean_comments((arithmetic / "SievePrimeCounting.lean").read_text())
    counter = source.split("def sievePrimeCount", 1)[1].split("theorem", 1)[0]
    assert "Nat.bitCountBlockPacked k bits 1 (wheelLength n - 1)" in counter
    assert "Nat.bitCountBlockPacked_eq_card" in source
    source = strip_lean_comments((arithmetic / "SievePrimeCountIncrements.lean").read_text())
    assert "Nat.bitCountBlockPacked_eq] at hc" in source


def test_primorial_rows_check_full_coverage_and_compose() -> None:
    arithmetic = ROOT / "PrimeFactorUnimodality/Helpers/Arithmetic"
    source = strip_lean_comments((arithmetic / "SievePrimeProduct.lean").read_text())
    assert "row.width ≤ 2 ^ row.depth" in source
    assert "(rows.map width).sum = wheelLength n - 1" in source
    assert "checkTrace bits 1 rows" in source
    assert "theorem checkTrace_append" in source
    assert "theorem primorial_eq_of_check" in source


def test_theta_anchor_uses_scaled_product_not_per_prime_logs() -> None:
    analytic = ROOT / "PrimeFactorUnimodality/Helpers/Analytic"
    source = strip_lean_comments((analytic / "NaturalLogScaling.lean").read_text())
    checker = source.split("def check", 1)[1].split("theorem", 1)[0]
    assert "row.lower * 2 ^ row.exponent ≤ value" in checker
    assert "value ≤ row.upper * 2 ^ row.exponent" in checker
    assert "c.log value" not in source
    source = strip_lean_comments((analytic / "SievedThetaAnchor.lean").read_text())
    assert "Chebyshev.theta_eq_log_primorial" in source
    assert "SieveProductRow.primorial_eq_of_check" in source
    assert "primeCounting_eq_of_sieve_check" in source
