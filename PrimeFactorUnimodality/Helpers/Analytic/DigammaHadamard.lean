import PrimeNumberTheoremAnd.Mathlib.Analysis.SpecialFunctions.Gamma.DigammaSeries

/-! # The shifted gamma poles as a regularized resolvent series

The poles of `Gamma(z/2+1)` are the negative even integers. Their
three-halves moment is a convergent real p-series. The digamma expansion
is rewritten using the same genus-one atoms as the xi contour argument.
We use Robby Sneiderman's Apache-2.0 `Complex.hasSum_digamma_of_re_pos`
from `kimihiro64/PrimeNumberTheoremAnd`, revision
`f6147e7572ab3abe5428101bc0b13627bcb005df`, module `DigammaSeries`.
-/

namespace PrimeFactorUnimodality

noncomputable section

open Complex

/-- The poles of the shifted gamma factor, starting at minus two. -/
def shiftedGammaPole (n : ℕ) : ℂ := -(2 * ((n : ℂ) + 1))

/-- No shifted gamma pole is the origin. -/
theorem shiftedGammaPole_ne_zero (n : ℕ) : shiftedGammaPole n ≠ 0 := by
  unfold shiftedGammaPole
  exact neg_ne_zero.mpr (mul_ne_zero (by norm_num) (Nat.cast_add_one_ne_zero n))

/-- All shifted gamma poles lie strictly left of any positive contour. -/
theorem shiftedGammaPole_re_nonpos (n : ℕ) : (shiftedGammaPole n).re ≤ 0 := by
  have heq : (shiftedGammaPole n).re = -2 * ((n : ℝ) + 1) := by simp [shiftedGammaPole]
  rw [heq]
  have := Nat.cast_nonneg (α := ℝ) n
  linarith

/-- The moment needed by absolute contour interchange is an ordinary p-series. -/
theorem summable_shiftedGammaPole_norm_inv_rpow :
    Summable (fun n : ℕ => ‖shiftedGammaPole n‖⁻¹ ^ (3 / 2 : ℝ)) := by
  have hp := (summable_nat_add_iff 1).mpr
    (Real.summable_nat_rpow_inv.mpr (by norm_num : (1 : ℝ) < 3 / 2))
  have hp' : Summable (fun n : ℕ => ((n : ℝ) + 1)⁻¹ ^ (3 / 2 : ℝ)) := by
    apply hp.congr
    intro n
    simp only [Nat.cast_add, Nat.cast_one]
    rw [Real.inv_rpow (by positivity)]
  apply (hp'.mul_left ((2 : ℝ)⁻¹ ^ (3 / 2 : ℝ))).congr
  intro n
  rw [shiftedGammaPole, norm_neg, norm_mul, norm_natCast_add_one]
  norm_num only [norm_ofNat]
  rw [mul_inv, Real.mul_rpow (by positivity) (by positivity)]
  simp only [one_div]

/-- Each digamma term is minus twice the corresponding regularized pole atom. -/
theorem digamma_term_eq_shiftedGamma_atom {z : ℂ} (hz : 0 < z.re) (n : ℕ) :
    ((n : ℂ) + 1)⁻¹ - (z / 2 + 1 + n)⁻¹ =
      -2 * (1 / (z - shiftedGammaPole n) + 1 / shiftedGammaPole n) := by
  have hn : (n : ℂ) + 1 ≠ 0 := Nat.cast_add_one_ne_zero n
  have hzn : z / 2 + 1 + n ≠ 0 := by
    intro heq
    have hre := congrArg Complex.re heq
    simp only [add_re, div_ofNat_re, one_re, natCast_re, zero_re] at hre
    have := Nat.cast_nonneg (α := ℝ) n
    linarith
  have heq : z - shiftedGammaPole n = 2 * (z / 2 + 1 + n) := by
    unfold shiftedGammaPole
    ring
  rw [heq, shiftedGammaPole]
  field_simp
  ring

/-- The shifted digamma expansion with the same regularization as the xi divisor. -/
theorem digamma_half_add_one_eq_shiftedGamma_tsum {z : ℂ} (hz : 0 < z.re) :
    digamma (z / 2 + 1) = -(Real.eulerMascheroniConstant : ℂ) -
      2 * ∑' n : ℕ, (1 / (z - shiftedGammaPole n) + 1 / shiftedGammaPole n) := by
  have hs := (Complex.hasSum_digamma_of_re_pos
    (z₀ := z / 2 + 1) (by simp only [add_re, div_ofNat_re, one_re]; linarith)).tsum_eq
  simp_rw [digamma_term_eq_shiftedGamma_atom hz] at hs
  rw [tsum_mul_left] at hs
  linear_combination -hs

end

end PrimeFactorUnimodality
