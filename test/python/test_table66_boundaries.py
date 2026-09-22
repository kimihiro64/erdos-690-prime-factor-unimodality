"""Keep the theta-table proof infrastructure independent of finite replays."""

from __future__ import annotations

import re
from pathlib import Path

from scripts.lean_source import lean_imports, strip_lean_comments

ROOT = Path(__file__).resolve().parents[2]
ANALYTIC = ROOT / "PrimeFactorUnimodality/Helpers/Analytic"


def test_subinterval_assembler_has_no_generated_dependencies() -> None:
    pending = [
        "PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.Table66EndpointFacts",
        "PrimeFactorUnimodality.Helpers.Analytic.DusartThetaClosedPart01",
        "PrimeFactorUnimodality.Helpers.Analytic.DusartThetaClosedPart02",
        "PrimeFactorUnimodality.Helpers.Analytic.DusartPrimeCountingAssembly",
    ]
    visited: set[str] = set()
    while pending:
        module = pending.pop()
        if module in visited:
            continue
        visited.add(module)
        assert ".Generated." not in module
        assert module != "PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows"
        assert not re.search(r"\.DusartProof(?:Part\d+)?$", module)
        path = ROOT.joinpath(*module.split(".")).with_suffix(".lean")
        if path.is_file():
            pending.extend(lean_imports(strip_lean_comments(path.read_text())))


def test_endpoint_facts_require_covering_cells() -> None:
    code = strip_lean_comments(
        (ANALYTIC / "FinitePrimeIntervalRows/Table66EndpointFacts.lean").read_text()
    )
    assert "cells : ∃ cells : List DusartThetaTable66Cell" in code
    assert "DusartThetaTable66CellsCover data cells" in code
    assert "lower_one_endpoint" not in code
    assert "upper_one_endpoint" not in code


def test_prime_count_assembly_does_not_require_a_false_small_theta_estimate() -> None:
    code = strip_lean_comments((ANALYTIC / "DusartPrimeCountingAssembly.lean").read_text())
    assert "HasThetaLogFourthErrorBelow" not in code
    assert "wangCrapis_primeCounting_of_paper_theta_estimates" in code
    assert "lowerAnchor : dusartM 2 x₀ ≤ dusartJ 3 (-1) x₀ x₀" in code
    assert "upperAnchor : dusartJ 2 (1 / 20) x₀ x₀ ≤ dusartM (1167 / 500) x₀" in code


def test_zeta_ingredients_are_independent_and_checked_before_consumers() -> None:
    pole = strip_lean_comments((ANALYTIC / "ZetaRealPole.lean").read_text())
    assert lean_imports(pole) == [
        "PrimeFactorUnimodality.Mathlib.NumberTheory.LSeries.ZetaTrigonometric",
        "PrimeNumberTheoremAnd.Mathlib.NumberTheory.LSeries.RiemannZetaAbelContinuation",
    ]
    assert "HasDusart" not in pole
    workflow = (ROOT / ".github/workflows/ci.yml").read_text()
    pole_target = "+PrimeFactorUnimodality.Helpers.Analytic.ZetaRealPole"
    consumer = "+PrimeFactorUnimodality.Helpers.Analytic.ZetaExplicitBounds"
    regression = "lake env lean test/lean/ZetaZeroFreeIngredients.lean"
    assert workflow.index(pole_target) < workflow.index(regression) < workflow.index(consumer)


def test_old_first_row_endpoints_are_incompatible() -> None:
    # Lean proves log(200000000) >= 1; even this weaker margin contradicts
    # the simultaneous theta(100000000) upper endpoint requirement.
    assert 200000000 - 550000 > 99998000


def test_table_adapter_keeps_finite_prefix_separate() -> None:
    facts = strip_lean_comments(
        (ANALYTIC / "FinitePrimeIntervalRows/Table66EndpointFacts.lean").read_text()
    )
    assert "(hprefix : HasDusartSymmetricThetaBoundsBelow x₀)" in facts
    assert "(cover : ∀ x : Real, x₀ ≤ x → x ≤ X →" in facts
    tail = strip_lean_comments((ANALYTIC / "DusartThetaClosedPart02.lean").read_text())
    assert "(h2x₀.trans hx)" not in tail
    assert "have table : HasDusartSymmetricThetaBoundsBelow X" not in tail


def test_split_theta_modules_have_balanced_scopes() -> None:
    for name in ("DusartThetaClosedPart01.lean", "DusartThetaClosedPart01Tail.lean"):
        code = strip_lean_comments((ANALYTIC / name).read_text())
        assert len(re.findall(r"(?m)^namespace \w+\s*$", code)) == 1
        assert len(re.findall(r"(?m)^noncomputable section\s*$", code)) == 1
        assert len(re.findall(r"(?m)^end(?: [A-Za-z0-9_.]+)?\s*$", code)) == 2


def test_theta_tail_declares_helpers_before_consumers() -> None:
    code = strip_lean_comments((ANALYTIC / "DusartThetaClosedPart01Tail.lean").read_text())
    assert "theorem wangCrapis_explicit_log_derivative_input :" in code
    assert code.index("theorem wangCrapis_thetaBounds_of_logFourthTail") < code.index(
        "theorem wangCrapis_thetaBounds_of_indexed_endpoint_rows_and_tail"
    )
    assert code.index("theorem wangCrapis_thetaBounds_of_paper_ranges_and_prop31_thetaError") < (
        code.index("theorem wangCrapis_thetaBounds_of_table66_and_prop31_thetaError")
    )


def test_ci_checks_subintervals_and_lean_regressions() -> None:
    workflow = (ROOT / ".github/workflows/ci.yml").read_text()
    assert (
        "+PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.Table66Subintervals"
        in (workflow)
    )
    assert "lake env lean test/lean/Table66Subintervals.lean" in workflow
    assert "lake env lean test/lean/DusartAnalytic.lean" in workflow


def test_prime_power_helpers_precede_intermediate_consumers() -> None:
    power = strip_lean_comments((ANALYTIC / "DusartPrimePower.lean").read_text())
    imports = lean_imports(
        strip_lean_comments((ANALYTIC / "DusartIntermediatePower.lean").read_text())
    )
    assert "PrimeFactorUnimodality.Helpers.Analytic.DusartPrimePower" in imports
    assert "theorem dusart_rpow_ratio_bound" in power
    assert "theorem dusart_lemma_3_3_prime_power_decomposition" in power
    for name in ("DusartProofPart05.lean", "DusartProofPart06.lean"):
        code = strip_lean_comments((ANALYTIC / name).read_text())
        assert "theorem dusart_rpow_ratio_bound" not in code
        assert "theorem dusart_lemma_3_3_prime_power_decomposition" not in code


def test_prime_count_certificates_do_not_import_the_medium_pnt() -> None:
    pending = [
        "PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.PrimeCountingCertificates"
    ]
    visited: set[str] = set()
    while pending:
        module = pending.pop()
        if module in visited:
            continue
        visited.add(module)
        assert not module.endswith(".MediumPNT")
        assert not module.endswith(".FinitePrimeIntervalRows.Core")
        path = ROOT.joinpath(*module.split(".")).with_suffix(".lean")
        if path.is_file():
            pending.extend(lean_imports(strip_lean_comments(path.read_text())))


def test_short_interval_tail_precedes_its_consumers() -> None:
    code = strip_lean_comments((ANALYTIC / "DusartShortIntervalClosed.lean").read_text())
    assert code.index("theorem wangCrapis_logCubedTail_of_thetaLogFourthError") < code.index(
        "theorem wangCrapis_shortInterval_of_selected_cutoff"
    )


def test_finite_facade_has_no_duplicate_declarations() -> None:
    code = strip_lean_comments((ANALYTIC / "FinitePrimeIntervalRows.lean").read_text())
    names = re.findall(r"(?m)^(?:theorem|def|structure) ([A-Za-z0-9_.]+)", code)
    assert len(names) == len(set(names))


def test_finite_facade_declares_helpers_before_consumers() -> None:
    code = "\n".join(
        strip_lean_comments((ANALYTIC / path).read_text())
        for path in (
            "FinitePrimeIntervalRows/ThetaRows.lean",
            "FinitePrimeIntervalRows/ThetaEndpointRows.lean",
            "FinitePrimeIntervalRows/PrimeCountingRows.lean",
            "FinitePrimeIntervalRows/Table66Rows.lean",
            "FinitePrimeIntervalRows/Table66Assembly.lean",
        )
    )
    for name in (
        "strictThetaUpperRow_provides",
        "DusartThetaEndpointRowsCoverUpTo",
        "dusartThetaEndpointRow_provides",
        "dusartPrimeCountingEndpointRow_provides",
        "DusartThetaRelativeIndexedCoverUpTo",
        "hasDusartSymmetricThetaBoundsBelow_of_indexed_relative_rows",
    ):
        declaration = re.search(rf"(?m)^(?:theorem|def) ({name})\b", code)
        assert declaration is not None
        assert code.index(name) == declaration.start(1)
    for name in (
        "dusartThetaEndpointRow_provides",
        "dusartThetaRelativeRow_provides",
        "dusartThetaTable66Row_provides_zero",
    ):
        assert f"def {name}\n" in code
        assert f"theorem {name}\n" not in code


def test_relative_rows_keep_pointwise_logarithmic_lower_bound() -> None:
    code = strip_lean_comments((ANALYTIC / "FinitePrimeIntervalRows/ThetaRows.lean").read_text())
    assert "upper_coeff_le_one : upper_coeff ≤ 1" in code
    assert "lower_error : ∀ x : Real" in code
    assert "formula.lower_one x hleft hright" in code
    assert "Real.log (row.right" not in code


def test_singleton_is_not_used_as_real_prefix_coverage() -> None:
    code = strip_lean_comments((ANALYTIC / "DusartThetaClosedPart01.lean").read_text())
    assert "dusartThetaEndpointRow_three_cover" not in code
    assert "theta_nat_lt_id_small" in code
    prime_rows = strip_lean_comments(
        (ANALYTIC / "FinitePrimeIntervalRows/PrimeCountingRows.lean").read_text()
    )
    assert "∀ x : Real, (1000 : Real) ≤ x → x ≤ 1000 →" in prime_rows
    assert "rw [← computablePrimesBelow_succ_length]" in prime_rows
