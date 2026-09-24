import PrimeFactorUnimodality.Mathlib.Analysis.Complex.HorizontalIntegral
import PrimeFactorUnimodality.Mathlib.Analysis.SpecialFunctions.Gamma.StripBound
import PrimeFactorUnimodality.Mathlib.Analysis.SpecialFunctions.Gaussian.PolynomialDecay

/-! Positive-strip Gamma bounds retain every signed imaginary height. -/

open scoped Topology

example (t : ℝ) : ‖Complex.Gamma (1 + (t : ℂ) * Complex.I)‖ ≤ 1 := by
  simpa using Complex.norm_Gamma_le_real_Gamma
    (s := 1 + (t : ℂ) * Complex.I) (by simp)

example (t : ℝ) {s : ℝ} (hs : s ∈ Set.Icc 1 2) :
    ‖Complex.Gamma ((s : ℂ) + (t : ℂ) * Complex.I)‖ ≤ 1 := by
  simpa using Complex.norm_Gamma_le_max_of_re_mem_Icc
    (a := 1) (b := 2) (by norm_num) (by norm_num)
    (s := (s : ℂ) + (t : ℂ) * Complex.I) (by simpa using hs)

example (k : ℕ) {b : ℝ} (hb : 0 < b) :
    Filter.Tendsto (fun x : ℝ => x ^ k * Real.exp (-b * x ^ 2)) Filter.atTop (𝓝 0) :=
  Real.tendsto_pow_mul_exp_neg_mul_sq k hb
