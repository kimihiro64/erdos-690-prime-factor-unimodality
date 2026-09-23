import PrimeFactorUnimodality.Helpers.Analytic.ComplexRotationIntervals
import PrimeFactorUnimodality.Helpers.Analytic.ZetaGridValueIntervals

/-! # Rational margins for the existing actual xi-grid sign interface

A sample stores a short correction, a phase approximation and scalar caps.
Its value uses retained Fourier arrays. Rotation intervals and a rational
norm comparison bound the complete xi error, including the Gamma remainder.
Strict separation gives either sign orientation of the existing evaluator.
-/

namespace PrimeFactorUnimodality

open Complex LeanCert.Core

/-- Per-sample rational data; the long moments and transforms live in the shared block. -/
structure XiGridSignData where
  point : RationalGridPoint
  phase : ℚ
  phaseError : ℚ
  turns : ℤ
  valueCap : ℚ
  risingCap : ℚ
  tailCap : ℚ
  positive : Bool

namespace XiGridSignData

/-- Retain the Euler, shared, short-correction, Gamma and phase errors. -/
def budget (s : XiGridSignData) (sharedCap : ℚ) : ℚ :=
  s.tailCap + sharedCap + s.point.error + s.valueCap * (1 / 10 + s.phaseError)

/-- A short Fourier polynomial enclosure, rotated by the stored rational phase. -/
def rotated (s : XiGridSignData) (r : RationalGridRows) (degree : ℕ)
    (c : SharedTaylorIntervals) (P : IntervalRat) : ComplexInterval :=
  (ComplexInterval.rotation c P (IntervalRat.singleton s.phase) s.turns).mul
    (r.valueInterval s.point P degree)

/-- Both sign orientations require strict separation from the full error. -/
def checkMargin (s : XiGridSignData) (r : RationalGridRows) (degree : ℕ)
    (c : SharedTaylorIntervals) (P : IntervalRat) (sharedCap : ℚ) : Bool :=
  (r.valueInterval s.point P degree).close ⟨0, 0⟩ s.valueCap &&
    decide (0 ≤ s.phaseError ∧ if s.positive then
      s.budget sharedCap < (s.rotated r degree c P).re.lo
    else (s.rotated r degree c P).re.hi < -s.budget sharedCap)

/-- Accepted margins satisfy the original complete-error inequalities, in either orientation. -/
theorem margin_of_check (s : XiGridSignData) (r : RationalGridRows) (d : ZetaGroupedBlock)
    {c : SharedTaylorIntervals} (hc : c.Prepared) {P : IntervalRat} (hpi : Real.pi ∈ P)
    (sharedCap : ℚ)
    (he : s.point.toGridPoint.error (r.attach d) ≤
      ((s.tailCap + sharedCap + s.point.error : ℚ) : ℝ))
    (h : s.checkMargin r d.degree c P sharedCap = true) :
    if s.positive then
      s.point.toGridPoint.xiError (r.attach d) s.phaseError <
        s.point.toGridPoint.xiApprox (r.attach d) s.phase
    else s.point.toGridPoint.xiApprox (r.attach d) s.phase <
      -s.point.toGridPoint.xiError (r.attach d) s.phaseError := by
  simp only [checkMargin, Bool.and_eq_true, decide_eq_true_eq] at h
  have hv := r.mem_valueInterval d s.point hpi
  have hn := ComplexInterval.norm_le_of_close_zero h.1 hv
  have hrot : exp (I * (s.phase : ℂ)) * s.point.toGridPoint.value (r.attach d) ∈
      s.rotated r d.degree c P :=
    ComplexInterval.mem_rotated hc hpi (IntervalRat.mem_singleton s.phase) s.turns hv
  have hδ : (0 : ℝ) ≤ 1 / 10 + (s.phaseError : ℝ) := by
    have hδ' : (0 : ℝ) ≤ s.phaseError := by exact_mod_cast h.2.1
    linarith
  have hb : s.point.toGridPoint.xiError (r.attach d) s.phaseError ≤
      (s.budget sharedCap : ℝ) := by
    have hm := add_le_add he (mul_le_mul_of_nonneg_right hn hδ)
    simpa only [ZetaGridPoint.xiError, budget, Rat.cast_add, Rat.cast_mul, Rat.cast_div,
      Rat.cast_one, Rat.cast_ofNat] using hm
  cases hs : s.positive with
  | true =>
    simp only [hs, ↓reduceIte] at h ⊢
    have hlt : (s.budget sharedCap : ℝ) < ((s.rotated r d.degree c P).re.lo : ℝ) :=
      by exact_mod_cast h.2.2
    exact (hb.trans_lt hlt).trans_le hrot.1.1
  | false =>
    simp only [hs, Bool.false_eq_true, ↓reduceIte] at h ⊢
    have hlt : ((s.rotated r d.degree c P).re.hi : ℝ) < -(s.budget sharedCap : ℝ) :=
      by exact_mod_cast h.2.2
    exact (hrot.1.2.trans_lt hlt).trans_le (neg_le_neg hb)

end XiGridSignData

end PrimeFactorUnimodality
