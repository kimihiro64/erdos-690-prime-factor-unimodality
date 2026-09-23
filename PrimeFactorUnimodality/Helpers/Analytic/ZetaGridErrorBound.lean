import PrimeFactorUnimodality.Helpers.Analytic.ZetaGridEvaluation

/-! # Shared error majorants for every point in a Fourier window

Within the unit coordinate window, all powers have absolute value at most
one. This bounds moment and transform errors by sums computed once per
block. Exact Fourier phases contribute zero error, but the Euler tail,
Taylor truncation, stored moments and short correction are all retained.
-/

namespace PrimeFactorUnimodality

noncomputable section

open Complex Finset Fourier

/-- One shared sum bounds all the weighted moment and transform errors. -/
theorem ZetaGridPoint.error_le_shared {d : ZetaGridBlock} (hd : d.Valid)
    (p : ZetaGridPoint) (hp : |p.coordinate d| ≤ 1) :
    p.error d ≤ zetaEulerError d.shared.cutoff ((1 / 2 : ℂ) + p.height d * I) d.shared.order +
      d.shared.cutoff * ((1 / 2 : ℝ) ^ d.shared.degree * Real.exp (1 / 2)) +
      (∑ b ∈ d.shared.groups, ∑ j ∈ range d.shared.degree, d.shared.coefficientError b j) +
      p.correctionError + ∑ j ∈ range d.shared.degree, (d.trace j).error := by
  have hm : (∑ b ∈ d.shared.groups, ∑ j ∈ range d.shared.degree,
      d.shared.coefficientError b j * |p.coordinate d| ^ j) ≤
      ∑ b ∈ d.shared.groups, ∑ j ∈ range d.shared.degree, d.shared.coefficientError b j := by
    apply sum_le_sum
    intro b hb
    apply sum_le_sum
    intro j hj
    exact mul_le_of_le_one_right ((norm_nonneg _).trans (hd.1.moments b hb j hj))
      (pow_le_one₀ (abs_nonneg _) hp)
  have ht : p.transformError d ≤ ∑ j ∈ range d.shared.degree, (d.trace j).error := by
    apply sum_le_sum
    intro j hj
    exact mul_le_of_le_one_right ((hd.2 j hj).error_nonneg (by
      simp [ZMod.stdAddChar_apply])) (pow_le_one₀ (abs_nonneg _) hp)
  simp only [ZetaGridPoint.error, ZetaGroupedPoint.error, ZetaGroupedPoint.roundingBudget,
    ZetaGridPoint.asGrouped, ZetaGroupedPoint.height, mul_zero, add_zero]
  change _ + (_ + _ + _) + _ ≤ _
  dsimp only [ZetaGridPoint.height] at *
  linarith

end

end PrimeFactorUnimodality
