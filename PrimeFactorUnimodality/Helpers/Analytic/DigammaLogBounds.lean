import PrimeFactorUnimodality.Helpers.Analytic.DigammaEulerBounds
import PrimeFactorUnimodality.Mathlib.Analysis.SpecialFunctions.Complex.LogShiftLimit
import PrimeNumberTheoremAnd.Mathlib.Analysis.SpecialFunctions.Gamma.DigammaSeries

/-! # A two-sided explicit logarithmic approximation to digamma

The actual PNT digamma series and Mathlib's Euler-constant limit identify
the limit of the reciprocal partial sums. Passing the uniform finite
Euler--Maclaurin bound to this limit gives `norm(digamma(z)-log(z))<=1/Re(z)`.
Unlike a constant lower bound, this retains the logarithmic leading term
when the shifted Gamma factors are subtracted.
-/

namespace PrimeFactorUnimodality

noncomputable section

open Complex Filter
open scoped Topology

/-- The reciprocal partial sums, with their real logarithmic normalization, tend to digamma. -/
theorem tendsto_sum_inv_add_sub_log {z : ℂ} (hz : 0 < z.re) :
    Tendsto (fun N : ℕ => (∑ k ∈ Finset.range (N + 1), (z + (k : ℂ))⁻¹) -
      (Real.log ((N : ℝ) + 1) : ℂ)) atTop (𝓝 (-digamma z)) := by
  have hS := (Complex.hasSum_digamma_of_re_pos hz).tendsto_sum_nat.comp
    (tendsto_add_atTop_nat 1)
  have hH := (Real.tendsto_harmonic_sub_log.comp (tendsto_add_atTop_nat 1)).ofReal
  convert! hH.sub hS using 1
  · funext N
    dsimp only [Function.comp_apply]
    rw [Finset.sum_sub_distrib, Complex.sum_inv_natCast_add_one]
    push_cast
    ring
  · congr 1
    ring

/-- Uniform approximation on the full open right half-plane, with an explicit constant. -/
theorem norm_digamma_sub_log_le_inv_re {z : ℂ} (hz : 0 < z.re) :
    ‖digamma z - Complex.log z‖ ≤ 1 / z.re := by
  have h := ((tendsto_sum_inv_add_sub_log hz).sub
    (Complex.tendsto_log_add_nat_sub_log_nat_add_one z)).add_const (Complex.log z)
  have hl : Tendsto (fun N : ℕ =>
      ‖(∑ k ∈ Finset.range (N + 1), (z + (k : ℂ))⁻¹) -
        (Complex.log (z + (N : ℂ)) - Complex.log z)‖)
      atTop (𝓝 ‖Complex.log z - digamma z‖) := by
    convert! h.norm using 1
    · funext N
      congr 1
      abel
    · congr 2
      ring
  have hb := le_of_tendsto hl (Filter.Eventually.of_forall (norm_sum_inv_add_sub_log_le hz))
  rwa [norm_sub_rev] at hb

/-- Both real-part inequalities follow from the same actual complex estimate. -/
theorem abs_re_digamma_sub_log_norm_le {z : ℂ} (hz : 0 < z.re) :
    |(digamma z).re - Real.log ‖z‖| ≤ 1 / z.re := by
  simpa only [sub_re, Complex.log_re] using
    (abs_re_le_norm (digamma z - Complex.log z)).trans (norm_digamma_sub_log_le_inv_re hz)

end

end PrimeFactorUnimodality
