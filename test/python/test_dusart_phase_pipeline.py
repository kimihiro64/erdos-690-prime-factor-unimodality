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
