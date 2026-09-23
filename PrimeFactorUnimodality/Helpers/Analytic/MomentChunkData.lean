import PrimeFactorUnimodality.Helpers.Analytic.DirichletAtomIntervals
import PrimeFactorUnimodality.Helpers.Analytic.MomentIntervalColumns

/-! # Shared data and residual checks for consecutive moment chunks

Rational and interval-valued block parameters use the same chunk data,
column output and half-unit residual criterion. The numerical atom builder
is separate from their common finite-moment assembler.
-/

namespace PrimeFactorUnimodality

open LeanCert.Core

/-- A bounded consecutive group of atoms with one shared integer frequency bin. -/
structure MomentIntervalChunk where
  first : ℕ
  count : ℕ
  group : ℤ
  turns : Vector ℤ count

/-- One shared evaluation result for all residual and coefficient checks. -/
structure MomentChunkEvaluation (degree : ℕ) where
  residuals : Bool
  columns : Vector ComplexInterval degree

/-- Both rational endpoints must lie in the full permitted residual window. -/
def residualWithinHalf (R : IntervalRat) : Bool :=
  decide (-(1 / 2 : ℚ) ≤ R.lo ∧ R.hi ≤ (1 / 2 : ℚ))

/-- The residual test proves the actual half-unit bound, including both endpoints. -/
theorem abs_le_half_of_residualWithinHalf {R : IntervalRat}
    (h : residualWithinHalf R = true) {x : ℝ} (hx : x ∈ R) : |x| ≤ (1 / 2 : ℝ) := by
  simp only [residualWithinHalf, decide_eq_true_eq] at h
  have hlo : ((-(1 / 2 : ℚ) : ℚ) : ℝ) ≤ (R.lo : ℝ) := Rat.cast_le.mpr h.1
  have hhi : (R.hi : ℝ) ≤ ((1 / 2 : ℚ) : ℝ) := Rat.cast_le.mpr h.2
  norm_num only [Rat.cast_neg, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat] at hlo hhi
  exact abs_le.mpr ⟨hlo.trans hx.1, hx.2.trans hhi⟩

end PrimeFactorUnimodality
