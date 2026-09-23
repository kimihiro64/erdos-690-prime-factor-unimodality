"""Keep the cancellation-preserving phase path connected and serial in CI."""

from pathlib import Path

from scripts.lean_source import strip_lean_comments

ROOT = Path(__file__).resolve().parents[2]
ANALYTIC = ROOT / "PrimeFactorUnimodality/Helpers/Analytic"
MODULES = (
    "Mathlib.MeasureTheory.Integral.IntervalIntegral.IteratedAverageScaling",
    "Mathlib.Analysis.SpecialFunctions.Complex.ExponentialStability",
    "Helpers.Analytic.DusartBoxOscillation",
    "Helpers.Analytic.DusartBoxPhaseBudget",
    "Helpers.Analytic.DusartBoxPhaseEvaluation",
    "Helpers.Analytic.DusartBoxPhaseGrid",
    "Mathlib.MeasureTheory.Integral.IntervalIntegral.IteratedAverageConjugation",
    "Helpers.Analytic.XiLowConjugatePartition",
    "Helpers.Analytic.XiZeroRowEnumeration",
    "Helpers.Analytic.XiTuringEnumeration",
    "Helpers.Analytic.DusartBoxPhaseConjugation",
    "Helpers.Analytic.DusartBoxPhaseRows",
    "Mathlib.MeasureTheory.Integral.IntervalIntegral.IteratedAverageStability",
    "Mathlib.MeasureTheory.Integral.IntervalIntegral.IteratedAverageVertical",
    "Helpers.Analytic.DusartBoxCoefficientStability",
    "Helpers.Analytic.DusartBoxCoefficientSamples",
    "Helpers.Analytic.DusartBoxRowErrors",
)


def test_phase_modules_and_regressions_are_serial_foundations() -> None:
    workflow = (ROOT / ".github/workflows/ci.yml").read_text()
    foundations = workflow.split("  lean-foundations:", 1)[1].split("  certificate-prebuild:", 1)[0]
    previous = foundations.index("lake env lean test/lean/GroupedGrid.lean")
    for module in MODULES:
        build = foundations.index(f"+PrimeFactorUnimodality.{module}\n")
        test = foundations.index(f"lake env lean test/lean/{module.rsplit('.', 1)[1]}.lean")
        assert previous < build < test
        previous = test


def test_phase_budget_keeps_actual_corrections_and_both_averages() -> None:
    source = strip_lean_comments((ANALYTIC / "DusartBoxPhaseBudget.lean").read_text())
    for required in (
        "smoothedXiPairedSum_box_eq_low_add_high",
        "norm_dusartBox_low_div_eq_phase",
        "norm_dusartBoxXiHighSum_div_le_power",
        "abs_dusartPsiAverageError_le_zero_sum",
        "dusart_abs_psi_div_le_of_relative_averages",
        "s / (1 - (m + 3 : \u2115) * s)",
        "|Chebyshev.psi x - x| / x",
        "Real.log (2 * Real.pi)",
    ):
        assert required in source
    assert "(hT : 10 < T)" in source
    assert "(hline :" in source
    assert "(hphase :" in source
    assert "norm_sum_dusartBox_xi_power_average_le" not in source


def test_phase_grid_reuses_shared_transforms_and_retains_all_errors() -> None:
    source = strip_lean_comments((ANALYTIC / "DusartBoxPhaseGrid.lean").read_text())
    for required in (
        "norm_dusartBoxLowPhaseSum_sub_grouped_le",
        "norm_exp_polynomial_grid_sub_traces_le",
        "(A ^ degree * Real.exp A)",
        "ε b j",
        "(t j).error",
        "(t j).Valid",
        "(k : \u2124)",
        "(aliasVector n B (fun b => a b j))",
    ):
        assert required in source


def test_phase_interpolation_uses_actual_ordinates_and_frequency_mass() -> None:
    source = strip_lean_comments((ANALYTIC / "DusartBoxPhaseEvaluation.lean").read_text())
    for required in (
        "norm_expSum_sub_expSum_le_of_enclosures",
        "norm_expSum_le_of_sample",
        "abs_dusartPsiAverageError_div_le_phase",
        "(Real.log x - u) - v",
        "‖z‖ + e + d * dusartBoxPhaseFrequencyMass m s u T",
    ):
        assert required in source


def test_rows_need_total_count_and_retain_one_family_for_every_weight() -> None:
    source = strip_lean_comments((ANALYTIC / "XiZeroRowEnumeration.lean").read_text())
    for required in (
        "(hcount : xiStrictZeroCount T ≤ n)",
        "(hf : Function.Injective f)",
        "eq_of_subset_of_card_le",
        "xiStrictPositiveHeightIndices T = univ.map ⟨f, hf⟩",
        "Set.Ioo ((rows i).lower : \u211d) (rows i).upper",
        "F (riemannXiDivisorConjugation (f i))",
    ):
        assert required in source
    statement = source.split("theorem Valid.exists_weighted_enumeration", 1)[1]
    assert statement.index("∃ f") < statement.index("∀ F") < statement.index(":= by")


def test_positive_rows_feed_actual_psi_and_preserve_real_part_cancellation() -> None:
    source = strip_lean_comments((ANALYTIC / "DusartBoxPhaseRows.lean").read_text())
    for required in (
        "h.exists_complete_indices ha hb hcount",
        "dusartBoxLowPhaseSum_eq_twice_re",
        "∃ \u03b3 : Fin n → \u211d",
        "∀ (m : \u2115) (s u v : \u211d)",
        "abs_re_le_norm",
        "2 * |z.re| + 2 * e",
        "abs_dusartPsiAverageError_div_le_phase",
        "h.low_criticalLine ha hb hcount",
        "h.strictCount_le_of_turing_padding hpad ha hmargin",
    ):
        assert required in source


def test_turing_padding_closes_the_actual_prefix_count() -> None:
    source = strip_lean_comments((ANALYTIC / "XiTuringEnumeration.lean").read_text())
    for required in (
        "exists_cover_of_count_integral",
        "(hpad : Valid padding a b)",
        "completedAreaRat (Fin.append rows padding)",
        "integral_xiZeroCountingRemainder_le_turingBudget",
        "xiStrictZeroCount (a : \u211d) ≤ n",
        "hpad.lower i",
        "h.exists_weighted_enumeration",
    ):
        assert required in source
    assert "(hcount :" not in source


def test_coefficient_sensitivity_uses_averages_not_difference_conditioning() -> None:
    source = strip_lean_comments((ANALYTIC / "DusartBoxCoefficientStability.lean").read_text())
    for required in (
        "norm_iteratedBoxAverageComplex_cpow_div_sub_le",
        "norm_rotated_sub_rotated_le",
        "1 / L ^ 2",
        "+ |u|",
        "(hL : 0 < L)",
        "(h\u03b3 : L ≤ \u03b3)",
        "norm_dusartBoxOrdinateCoefficient_sub_center_le",
    ):
        assert required in source
    assert "fwdDiff" not in source


def test_midpoint_samples_retain_power_phase_and_rounding_errors() -> None:
    source = strip_lean_comments((ANALYTIC / "DusartBoxCoefficientSamples.lean").read_text())
    for required in (
        "range (m + 4)",
        "(m + 3).choose j",
        "norm_fwdDiff_iter_sub_sum_le",
        "iteratedBoxAverageComplex_cpow_div_eq_difference",
        "dusartBoxCoefficientDenom_ne_zero",
        "cpowPrimitiveDenom_ne_zero",
        "norm_dusartBoxOrdinateCoefficient_sub_checked_samples_le",
        "* η + r",
    ):
        assert required in source


def test_midpoint_consumer_closes_universal_ordinate_and_completeness_inputs() -> None:
    source = strip_lean_comments((ANALYTIC / "DusartBoxRowErrors.lean").read_text())
    for required in (
        "norm_dusartBoxOrdinateCoefficient_sub_center_le",
        "norm_expSum_sub_expSum_le_of_enclosures",
        "h.abs_psi_average_le_of_turing_phase_enclosure",
        "dusartBoxRowsError rows m s u V c e + ε",
        "(hl : ∀ i, 0 < (rows i).lower)",
        "(hc : ∀ i, ‖dusartBoxOrdinateCoefficient m s u (rows i).center - c i‖ ≤ e i)",
    ):
        assert required in source
    statement = source.split("theorem XiSignRows.Valid.abs_psi_average_le_of_center_enclosures", 1)[
        1
    ]
    statement = statement.split(":= by", 1)[0]
    assert "∀ \u03b3" not in statement
    assert "(hcount :" not in statement
    assert "(hline :" not in statement
