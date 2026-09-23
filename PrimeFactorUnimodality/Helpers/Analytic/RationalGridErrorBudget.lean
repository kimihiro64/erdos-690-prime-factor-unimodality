import PrimeFactorUnimodality.Helpers.Analytic.CheckedZetaGridPoints
import PrimeFactorUnimodality.Helpers.Analytic.ZetaGridErrorBound

/-! # Check the height-independent grid error only once per block

The rational moment errors come from the checked moment rows. Their entire
sum, the complete recursive Fourier errors, and the Taylor truncation are
combined into one shared cap. Samples reuse its proof without traversing
the input rows or transform trees again.
-/

namespace PrimeFactorUnimodality

open Complex Finset Fourier LeanCert.Core

/-- Shared rational moment errors and a cap for every height-independent contribution. -/
structure RationalGridErrorBudget where
  moment : ℤ → ℕ → ℚ
  cap : ℚ

namespace RationalGridErrorBudget

/-- Sum every retained error; the exponential interval is prepared once per block. -/
def bound (b : RationalGridErrorBudget) (r : RationalGridRows) (N degree : ℕ)
    (expHalf : IntervalRat) : ℚ :=
  N * ((1 / 2 : ℚ) ^ degree * expHalf.hi) +
    (∑ k ∈ r.groups.toFinset, ∑ j ∈ range degree, b.moment k j) +
    ∑ j ∈ range degree, (r.trace j).error r.twiddles

/-- One rational comparison stores the complete shared budget. -/
def check (b : RationalGridErrorBudget) (r : RationalGridRows) (N degree : ℕ)
    (expHalf : IntervalRat) : Bool := decide (b.bound r N degree expHalf ≤ b.cap)

/-- No per-sample numerical sum remains after the shared check succeeds. -/
theorem error_le_of_check (b : RationalGridErrorBudget) (r : RationalGridRows)
    (d : ZetaGroupedBlock) (hd : (r.attach d).Valid)
    (hm : ∀ k j, d.coefficientError k j = (b.moment k j : ℝ))
    {expHalf : IntervalRat} (he : Real.exp (1 / 2) ∈ expHalf)
    (h : b.check r d.cutoff d.degree expHalf = true) (p : RationalGridPoint)
    (hp : |p.toGridPoint.coordinate (r.attach d)| ≤ 1) :
    p.toGridPoint.error (r.attach d) ≤
      zetaEulerError d.cutoff ((1 / 2 : ℂ) + p.toGridPoint.height (r.attach d) * I) d.order +
        b.cap + p.error := by
  have hbound := p.toGridPoint.error_le_shared hd hp
  have ht : (d.cutoff : ℝ) * ((1 / 2 : ℝ) ^ d.degree * Real.exp (1 / 2)) ≤
      d.cutoff * ((1 / 2 : ℝ) ^ d.degree * (expHalf.hi : ℝ)) :=
    mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left he.2 (by positivity))
      (Nat.cast_nonneg _)
  simp only [check, decide_eq_true_eq] at h
  have hb : (b.bound r d.cutoff d.degree expHalf : ℝ) ≤ (b.cap : ℝ) :=
    by exact_mod_cast h
  simp only [bound, Rat.cast_add, Rat.cast_mul, Rat.cast_natCast, Rat.cast_pow,
    Rat.cast_div, Rat.cast_one, Rat.cast_ofNat, Rat.cast_sum] at hb
  simp only [RationalGridRows.attach, RationalGridPoint.toGridPoint,
    RationalTrace.error_semantic, hm] at hbound
  dsimp only [RationalGridRows.attach, RationalGridPoint.toGridPoint]
  linarith

end RationalGridErrorBudget

end PrimeFactorUnimodality
