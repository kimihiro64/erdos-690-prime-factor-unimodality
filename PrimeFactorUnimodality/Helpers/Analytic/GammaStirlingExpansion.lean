import PrimeFactorUnimodality.Helpers.Analytic.GammaStirlingComplex
import PrimeFactorUnimodality.Mathlib.Analysis.SpecialFunctions.Complex.LogBernoulli
import PrimeFactorUnimodality.Mathlib.NumberTheory.BernoulliPeriodic.ShiftedRecursion

/-! # Arbitrary-order Stirling expansion of the actual complex Gamma logarithm

The exact second Bernoulli remainder fixes the initial coefficient. Repeated
integration by parts then gives every finite order with the full improper
remainder retained. No statement about the Gamma value is assumed.
-/

namespace PrimeFactorUnimodality

noncomputable section

open Complex Filter MeasureTheory Polynomial Set
open scoped Topology

/-- All finite Stirling corrections, retaining the zero odd Bernoulli coefficients. -/
def gammaStirlingCorrection (M : ℕ) (z : ℂ) : ℂ :=
  ∑ j ∈ Finset.range M,
    (j.factorial : ℂ) * (bernoulliNormalizedReal (j + 2) 0 : ℂ) * z⁻¹ ^ (j + 1)

/-- The first Stirling coefficient with its complete, absolutely convergent remainder. -/
theorem gammaRightLog_eq_stirling_first {z : ℂ} (hz : 0 < z.re) :
    gammaRightLog z = ((z - 1 / 2) * log z - z) +
      ((Real.log (2 * Real.pi) / 2 : ℝ) : ℂ) + (1 / 12 : ℂ) * z⁻¹ -
      ∫ x : ℝ in Ioi 0, (bernoulliPeriodic 2 x : ℂ) * (z + (x : ℂ))⁻¹ ^ 2 := by
  have hG := intervalIntegral_tendsto_integral_Ioi 0
    (integrableOn_bernoulliPeriodic_inv_pow 2 (by omega : 1 < 2) hz)
    (tendsto_natCast_atTop_atTop (R := ℝ))
  have hP : Tendsto (fun N : ℕ => (z + (N : ℂ))⁻¹) atTop (𝓝 0) := by
    simpa only [pow_one] using tendsto_inv_pow_add_nat (p := 1) (by omega) hz
  have hR := ((hP.sub_const z⁻¹).const_mul (1 / 12 : ℂ)).add hG
  have he : (fun N : ℕ => (1 / 12 : ℂ) * ((z + N)⁻¹ - z⁻¹) +
      ∫ x : ℝ in 0..(N : ℝ), (bernoulliPeriodic 2 x : ℂ) * (z + (x : ℂ))⁻¹ ^ 2) =
      (fun N : ℕ => ∑ k ∈ Finset.range N, logTrapezoidError z k (k + 1)) := by
    funext N
    exact (sum_logTrapezoidError_eq_bernoulli_two hz N).symm
  rw [he] at hR
  have h := tendsto_nhds_unique (tendsto_sum_logTrapezoidError hz) hR
  linear_combination -h

/-- Every positive truncation order has the exact factorial-weighted Bernoulli remainder. -/
theorem gammaRightLog_eq_stirling_expansion {z : ℂ} (hz : 0 < z.re)
    {M : ℕ} (hM : 1 ≤ M) :
    gammaRightLog z = ((z - 1 / 2) * log z - z) +
      ((Real.log (2 * Real.pi) / 2 : ℝ) : ℂ) + gammaStirlingCorrection M z -
      (M.factorial : ℂ) * ∫ x : ℝ in Ioi 0,
        (bernoulliPeriodic (M + 1) x : ℂ) * (z + (x : ℂ))⁻¹ ^ (M + 1) := by
  induction M with
  | zero => omega
  | succ M ih =>
    by_cases h0 : M = 0
    · subst M
      have hc : gammaStirlingCorrection 1 z = (1 / 12 : ℂ) * z⁻¹ := by
        norm_num [gammaStirlingCorrection, bernoulliNormalizedReal_zero, _root_.bernoulli_two]
      simpa only [Nat.reduceAdd, Nat.factorial_one, Nat.cast_one, one_mul, hc] using
        gammaRightLog_eq_stirling_first hz
    · have hMp : 1 ≤ M := by omega
      have hrec := bernoulliPeriodic_inv_pow_tail_recursion (k := M + 1) (p := M + 1)
        (by omega) (by omega) hz
      have hc : gammaStirlingCorrection (M + 1) z = gammaStirlingCorrection M z +
          (M.factorial : ℂ) * (bernoulliNormalizedReal (M + 2) 0 : ℂ) * z⁻¹ ^ (M + 1) := by
        unfold gammaStirlingCorrection
        rw [Finset.sum_range_succ]
      rw [ih hMp, hrec, hc, Nat.factorial_succ]
      push_cast
      ring

end

end PrimeFactorUnimodality
