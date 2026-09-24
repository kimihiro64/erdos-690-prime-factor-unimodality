"""Keep shared phase preparation separate from sample replay and preserve all proof inputs."""

from pathlib import Path

from scripts.lean_source import strip_lean_comments

ROOT = Path(__file__).resolve().parents[2]
ANALYTIC = "PrimeFactorUnimodality.Helpers.Analytic."


def source(name: str) -> str:
    return strip_lean_comments(
        (ROOT / "PrimeFactorUnimodality/Helpers/Analytic" / f"{name}.lean").read_text()
    )


def test_affine_targets_and_regressions_are_ordered_in_ci() -> None:
    workflow = (ROOT / ".github/workflows/ci.yml").read_text()
    base = workflow.index("lake env lean test/lean/XiSimplePhaseIntervals.lean")
    phase = workflow.index(f"+{ANALYTIC}XiAffinePhaseIntervals\n")
    phase_test = workflow.index("lake env lean test/lean/XiAffinePhaseIntervals.lean")
    packed = workflow.index("lake env lean test/lean/PackedXiGridMargins.lean")
    consumer = workflow.index(f"+{ANALYTIC}AffineXiGridSigns\n")
    consumer_test = workflow.index("lake env lean test/lean/AffineXiGridSigns.lean")
    assert base < phase < phase_test < packed < consumer < consumer_test


def test_preparation_is_checked_and_not_repeated_in_sample_phase_evaluation() -> None:
    code = source("XiAffinePhaseIntervals")
    preparation = code.split("def prepare", 1)[1].split("theorem prepare_valid", 1)[0]
    assert preparation.count("c.log H") == 1
    assert "intervalSubset prepared.value d.value" in code
    assert "intervalSubset prepared.slope d.slope" in code
    assert "mem_of_intervalSubset h.1.2 hp'.value" in code
    assert "mem_of_intervalSubset h.2 hp'.slope" in code
    sample = code.split("def affine", 1)[1]
    assert "SharedTaylorIntervals" not in sample
    assert "Real.log" not in sample and "c.log" not in sample
    assert "0 < d.base ∧ 0 < T.lo" in sample
    assert "33 / (16 * T.lo)" in sample
    assert "1 / 10 + (error : \u211d)" in sample
    assert "IntervalRat.add (d.affine T) (d.remainder T)" in sample


def test_affine_route_preserves_all_nonphase_checks() -> None:
    code = source("AffineXiGridSigns")
    assert "c.phaseData.check" not in code
    assert "d.check (c.height s.point) s.phase s.phaseError" in code
    assert "s.point.check c.rows.levels" in code
    assert "checkEulerRemainder c.endpoint" in code
    assert "s.checkCardinalMargin" in code and "s.checkSignMargin" in code
    assert "XiAffinePhaseIntervals.abs_counting_sub_le_of_check hd (mem_height hc s.point)" in code
    assert "exact sign_of_phase_bound" in code
    assert "Fin.strictMono_iff_lt_succ.mpr" in code
    assert "XiSignRow.valid_of_affine_grid" in code
    assert "p.margins_of_check hp hm i" in code
    assert "XiSignRows.CountSummary n A B" in code
    assert "XiSignRows.AreaSummary n A B a b area" in code
    assert "TuringMarginIntervals.low_criticalLine_of_check hm hc.scalar" in code


def test_common_sign_proof_does_not_require_the_old_phase_boolean() -> None:
    code = source("CheckedXiGridSigns")
    common = code.split("theorem sign_of_phase_bound", 1)[1].split("theorem sign_of_sign_check", 1)[
        0
    ]
    assert "c.phaseData.check" not in common
    assert "sign_of_check hc s" not in common
    assert "s.cardinal_phase_of_check" in common
    assert "s.projection_margin_of_check" in common
    assert "s.margin_of_check" in common
    assert "xiCriticalLineValue_pos_of_approx" in common
    assert "xiCriticalLineValue_neg_of_approx" in common
    assert "XiSimplePhaseIntervals.abs_counting_sub_le_of_check" in code
