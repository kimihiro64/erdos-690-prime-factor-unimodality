import PrimeFactorUnimodality.Mathlib.Analysis.SpecialFunctions.Integrals.LogDampedParameter

/-! # Exponential-cutoff domains, boundary cases and exact simplifications -/

namespace Real.Tests

example {a q p u : ℝ} (hpq : p < q) (hu : 1 < u) :
    exp (sqrt (a / (q - p))) ≤ u ↔ a ≤ (q - p) * log u ^ 2 :=
  logDampedPower_cutoff_iff hpq hu

example {a q u : ℝ} (ha : 0 ≤ a) (hu : 1 < u) :
    (∃ p : ℝ, 1 < p ∧ p < q ∧ exp (sqrt (a / (q - p))) ≤ u) ↔
      a < (q - 1) * log u ^ 2 :=
  exists_logDampedPower_cutoff_iff ha hu

-- A zero logarithmic margin cannot provide an integrable residual power.
example {a q u : ℝ} (ha : 0 ≤ a) (hu : 1 < u) (he : a = (q - 1) * log u ^ 2) :
    ¬ ∃ p : ℝ, 1 < p ∧ p < q ∧ exp (sqrt (a / (q - p))) ≤ u := by
  rw [exists_logDampedPower_cutoff_iff ha hu, he]
  exact lt_irrefl _

example {a q p b u : ℝ} (hpq : p < q) (hu : 1 < u) (ha : a ≤ (q - p) * log u ^ 2) :
    logDampedPowerMajorant a q p u * logDampedPowerIntegralFactor p b u =
      logDampedPower a q u *
        ((u / b) * (log (u / b) / (p - 1) + 1 / (p - 1) ^ 2) + 1 / p) :=
  logDampedPowerMajorant_mul_integralFactor hpq hu ha

example {q ν : ℝ} (hν : 0 < ν) (hmargin : 1 < (q - 1) * ν ^ 2) :
    1 < q - 1 / ν ^ 2 ∧ q - 1 / ν ^ 2 < q := logDampedPower_nu_exponent_mem hν hmargin

example : 1 < (4 : ℝ) - 1 / (1 : ℝ) ^ 2 ∧ (4 : ℝ) - 1 / (1 : ℝ) ^ 2 < 4 :=
  logDampedPower_nu_exponent_mem (by norm_num) (by norm_num)

example {q ν X : ℝ} (hX : 0 < X) (hν : 0 < ν) (hmargin : 1 < (q - 1) * ν ^ 2) :
    exp (sqrt (X ^ 2 / (q - (q - 1 / ν ^ 2)))) ≤ exp (ν * X) :=
  logDampedPower_nu_cutoff hX hν hmargin

example {q ν X : ℝ} (hX : 0 < X) (hν : 0 < ν) (hmargin : 1 < (q - 1) * ν ^ 2) :
    logDampedPowerMajorant (X ^ 2) q (q - 1 / ν ^ 2) (exp (ν * X)) = exp (-2 * X / ν) :=
  logDampedPowerMajorant_nu hX hν hmargin

example {q ν X : ℝ} (hX : 0 < X) (hν : 0 < ν) :
    logDampedPower (X ^ 2) q (exp (ν * X)) = exp (-q * (ν * X) - X / ν) :=
  logDampedPower_nu hX hν

example {q ν X : ℝ} (hX : 0 < X) (hν : 0 < ν) (hmargin : 1 < (q - 1) * ν ^ 2) :
    exp (sqrt (X ^ 2 / q)) ≤ exp (ν * X) := logDampedPower_nu_turn_le hX hν hmargin

example {q ν X b : ℝ} (hX : 0 < X) (hν : 0 < ν) (hb : 0 < b)
    (hmargin : 1 < (q - 1) * ν ^ 2) :
    logDampedPowerMajorant (X ^ 2) q (q - 1 / ν ^ 2) (exp (ν * X)) *
        logDampedPowerIntegralFactor (q - 1 / ν ^ 2) b (exp (ν * X)) =
      exp (-q * (ν * X) - X / ν) * logDampedNuIntegralFactor q ν X b :=
  logDampedPowerMajorant_nu_mul_integralFactor hX hν hb hmargin

example {q ν X b : ℝ} (hν : 0 < ν) (hb : 0 < b) (hmargin : 1 < (q - 1) * ν ^ 2)
    (hbu : b ≤ exp (ν * X)) : 0 < logDampedNuIntegralFactor q ν X b :=
  logDampedNuIntegralFactor_pos hν hb hmargin hbu

example {X ν : ℝ} (hν : 0 < ν) :
    exp (-X / ν) = exp (ν * X) * exp (-2 * X) * exp (-X * (1 - ν) ^ 2 / ν) :=
  exp_neg_div_eq_mul_exp_square hν

end Real.Tests
