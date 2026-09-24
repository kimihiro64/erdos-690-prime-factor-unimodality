import PrimeFactorUnimodality.Helpers.Analytic.CardinalRotationIntervals
import PrimeFactorUnimodality.Helpers.Analytic.XiGridSignIntervals

/-! # Xi sign margins without per-sample trigonometric evaluation

A rational midpoint selects a proposed integer quarter turn. Its distance
from the stored phase is then bounded using the complete pi interval, and
the Gamma and phase errors are retained. Selection is only a heuristic:
soundness follows from the strict phase guard, not from rounding accuracy.
The zeta approximation and all of its error contributions are unchanged.
-/

namespace PrimeFactorUnimodality.XiGridSignData

open Complex LeanCert.Core

/-- Propose a quarter turn using the pi midpoint; a separate check certifies its adequacy. -/
def cardinalQuarter (s : XiGridSignData) (P : IntervalRat) : ℤ :=
  ⌊4 * s.phase / (P.lo + P.hi) + 1 / 2⌋

/-- The full pi interval encloses the proposed exact angle, including large or negative turns. -/
def cardinalPhase (s : XiGridSignData) (P : IntervalRat) : IntervalRat :=
  IntervalRat.scale ((s.cardinalQuarter P : ℚ) / 2) P

/-- The complete bound on the phase displacement from the proposed exact quarter turn. -/
def cardinalPhaseBudget (s : XiGridSignData) (P : IntervalRat) : ℚ :=
  1 / 10 + s.phaseError + intervalPointRadius (s.cardinalPhase P) s.phase

/-- Select one signed component of the retained zeta approximation rectangle. -/
def cardinalProjection (s : XiGridSignData) (r : RationalGridRows) (degree : ℕ)
    (P : IntervalRat) : IntervalRat :=
  ComplexInterval.quarterRe (s.cardinalQuarter P) (r.valueInterval s.point P degree)

/-- A strict quarter-turn guard and full zeta-error separation certify either sign orientation. -/
def checkCardinalMargin (s : XiGridSignData) (r : RationalGridRows) (degree : ℕ)
    (P : IntervalRat) (sharedCap : ℚ) : Bool :=
  decide (0 ≤ s.phaseError ∧ s.cardinalPhaseBudget P < P.lo / 2 ∧ if s.positive then
    s.projectionBudget sharedCap < (s.cardinalProjection r degree P).lo
  else (s.cardinalProjection r degree P).hi < -s.projectionBudget sharedCap)

/-- The checked displacement bounds the true phase; rounding alone is never trusted. -/
theorem cardinal_phase_of_check (s : XiGridSignData) (r : RationalGridRows) (degree : ℕ)
    {P : IntervalRat} (hpi : Real.pi ∈ P) (sharedCap : ℚ)
    {θ : ℝ} (hθ : |θ - (s.phase : ℝ)| ≤ 1 / 10 + (s.phaseError : ℝ))
    (h : s.checkCardinalMargin r degree P sharedCap = true) :
    |θ - (s.cardinalQuarter P : ℝ) * Real.pi / 2| < Real.pi / 2 := by
  simp only [checkCardinalMargin, decide_eq_true_eq] at h
  have hmem : (s.cardinalQuarter P : ℝ) * Real.pi / 2 ∈ s.cardinalPhase P := by
    simpa [cardinalPhase, div_mul_eq_mul_div] using
      IntervalRat.mem_scale ((s.cardinalQuarter P : ℚ) / 2) hpi
  have hd := abs_sub_le_intervalPointRadius hmem s.phase
  rw [abs_sub_comm] at hd
  have hb : (s.cardinalPhaseBudget P : ℝ) < (P.lo : ℝ) / 2 := by exact_mod_cast h.2.1
  have ht := (abs_sub_le θ (s.phase : ℝ)
    ((s.cardinalQuarter P : ℝ) * Real.pi / 2)).trans (add_le_add hθ hd)
  have he : 1 / 10 + (s.phaseError : ℝ) +
      (intervalPointRadius (s.cardinalPhase P) s.phase : ℝ) =
      (s.cardinalPhaseBudget P : ℝ) := by simp [cardinalPhaseBudget]
  rw [he] at ht
  exact (ht.trans_lt hb).trans_le (div_le_div_of_nonneg_right hpi.1 (by norm_num))

/-- The signed-component enclosure supplies the exact rotated margin required by the sign lemma. -/
theorem cardinal_margin_of_check (s : XiGridSignData) (r : RationalGridRows)
    (d : ZetaGroupedBlock) {P : IntervalRat} (hpi : Real.pi ∈ P) (sharedCap : ℚ)
    (he : s.point.toGridPoint.error (r.attach d) ≤ (s.projectionBudget sharedCap : ℝ))
    (h : s.checkCardinalMargin r d.degree P sharedCap = true) :
    if s.positive then s.point.toGridPoint.error (r.attach d) <
      (exp (I * (((s.cardinalQuarter P : ℝ) * Real.pi / 2 : ℝ) : ℂ)) *
        s.point.toGridPoint.value (r.attach d)).re
    else (exp (I * (((s.cardinalQuarter P : ℝ) * Real.pi / 2 : ℝ) : ℂ)) *
        s.point.toGridPoint.value (r.attach d)).re < -s.point.toGridPoint.error (r.attach d) := by
  simp only [checkCardinalMargin, decide_eq_true_eq] at h
  have hv := ComplexInterval.mem_quarterRe (s.cardinalQuarter P)
    (r.mem_valueInterval d s.point hpi)
  cases hs : s.positive with
  | true =>
    simp only [hs, ↓reduceIte] at h ⊢
    have hm : (s.projectionBudget sharedCap : ℝ) < (s.cardinalProjection r d.degree P).lo :=
      by exact_mod_cast h.2.2
    exact (he.trans_lt hm).trans_le hv.1
  | false =>
    simp only [hs, Bool.false_eq_true, ↓reduceIte] at h ⊢
    have hm : ((s.cardinalProjection r d.degree P).hi : ℝ) < -(s.projectionBudget sharedCap : ℝ) :=
      by exact_mod_cast h.2.2
    exact (hv.2.trans_lt hm).trans_le (neg_le_neg he)

end PrimeFactorUnimodality.XiGridSignData
