/-
Copyright (c) 2026 Jonas Whidden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonas Whidden
-/
import PrimeFactorUnimodality.Mathlib.Analysis.SpecialFunctions.Integrals.LogDampedBound

/-! # Exponential cutoff parameters for logarithmically damped tails

The free exponent is chosen explicitly as `q-1/nu^2`. The exact condition
`1<(q-1)*nu^2` provides integrability and places the cutoff on the residual
kernel's turning point. No numerical choice of parameters is assumed.
-/

namespace Real

noncomputable section

/-- The turning-height condition is equivalent to a logarithmic polynomial inequality. -/
theorem logDampedPower_cutoff_iff {a q p u : ℝ} (hpq : p < q) (hu : 1 < u) :
    exp (sqrt (a / (q - p))) ≤ u ↔ a ≤ (q - p) * log u ^ 2 := by
  rw [← le_log_iff_exp_le (lt_trans zero_lt_one hu), sqrt_le_left (log_pos hu).le,
    div_le_iff₀ (sub_pos.mpr hpq)]
  rw [mul_comm (log u ^ 2)]

/-- After the remaining turning point, the integral coefficient cancels its split power. -/
theorem logDampedPowerMajorant_mul_integralFactor {a q p b u : ℝ}
    (hpq : p < q) (hu : 1 < u) (ha : a ≤ (q - p) * log u ^ 2) :
    logDampedPowerMajorant a q p u * logDampedPowerIntegralFactor p b u =
      logDampedPower a q u *
        ((u / b) * (log (u / b) / (p - 1) + 1 / (p - 1) ^ 2) + 1 / p) := by
  have hw := (logDampedPower_cutoff_iff hpq hu).mpr ha
  rw [logDampedPowerMajorant, ite_eq_left hw,
    logDampedPower_mul_integralFactor (lt_trans zero_lt_one hu)]

/-- An admissible cutoff exponent exists exactly when the logarithmic margin is positive. -/
theorem exists_logDampedPower_cutoff_iff {a q u : ℝ} (ha : 0 ≤ a) (hu : 1 < u) :
    (∃ p : ℝ, 1 < p ∧ p < q ∧ exp (sqrt (a / (q - p))) ≤ u) ↔
      a < (q - 1) * log u ^ 2 := by
  have hd : 0 < log u ^ 2 := sq_pos_of_pos (log_pos hu)
  constructor
  · rintro ⟨p, hp, hpq, hw⟩
    have he := (logDampedPower_cutoff_iff hpq hu).mp hw
    exact he.trans_lt (mul_lt_mul_of_pos_right (by linarith : q - p < q - 1) hd)
  · intro hmargin
    have hc : a / log u ^ 2 < q - 1 := (div_lt_iff₀ hd).mpr hmargin
    have hc0 : 0 ≤ a / log u ^ 2 := div_nonneg ha hd.le
    let p : ℝ := (q + 1 - a / log u ^ 2) / 2
    have hp : 1 < p := by dsimp [p]; linarith
    have hpq : p < q := by dsimp [p]; linarith
    refine ⟨p, hp, hpq, (logDampedPower_cutoff_iff hpq hu).mpr ?_⟩
    have hle : a / log u ^ 2 ≤ q - p := by dsimp [p]; linarith
    calc
      a = (a / log u ^ 2) * log u ^ 2 := (div_mul_cancel₀ a hd.ne').symm
      _ ≤ _ := mul_le_mul_of_nonneg_right hle hd.le

/-- The Rosser exponent is admissible under the exact squared-parameter condition. -/
theorem logDampedPower_nu_exponent_mem {q ν : ℝ} (hν : 0 < ν)
    (hmargin : 1 < (q - 1) * ν ^ 2) :
    1 < q - 1 / ν ^ 2 ∧ q - 1 / ν ^ 2 < q := by
  have hsq : 0 < ν ^ 2 := sq_pos_of_pos hν
  have he : 1 / ν ^ 2 < q - 1 := (div_lt_iff₀ hsq).mpr hmargin
  exact ⟨by linarith, sub_lt_self q (one_div_pos.mpr hsq)⟩

/-- The Rosser exponential cutoff reaches the remaining kernel's turning point. -/
theorem logDampedPower_nu_cutoff {q ν X : ℝ} (hX : 0 < X) (hν : 0 < ν)
    (hmargin : 1 < (q - 1) * ν ^ 2) :
    exp (sqrt (X ^ 2 / (q - (q - 1 / ν ^ 2)))) ≤ exp (ν * X) := by
  have hp := logDampedPower_nu_exponent_mem hν hmargin
  apply (logDampedPower_cutoff_iff hp.2 (one_lt_exp_iff.mpr (mul_pos hν hX))).mpr
  rw [log_exp]
  have he : (q - (q - 1 / ν ^ 2)) * (ν * X) ^ 2 = X ^ 2 := by
    field_simp
    ring
  exact he.ge

/-- The selected coefficient at the Rosser cutoff is a single exponential. -/
theorem logDampedPowerMajorant_nu {q ν X : ℝ} (hX : 0 < X) (hν : 0 < ν)
    (hmargin : 1 < (q - 1) * ν ^ 2) :
    logDampedPowerMajorant (X ^ 2) q (q - 1 / ν ^ 2) (exp (ν * X)) =
      exp (-2 * X / ν) := by
  rw [logDampedPowerMajorant, ite_eq_left (logDampedPower_nu_cutoff hX hν hmargin),
    logDampedPower, log_exp]
  congr 1
  field_simp
  ring

/-- The original kernel at an exponential cutoff has no logarithm or real power left. -/
theorem logDampedPower_nu {q ν X : ℝ} (hX : 0 < X) (hν : 0 < ν) :
    logDampedPower (X ^ 2) q (exp (ν * X)) = exp (-q * (ν * X) - X / ν) := by
  rw [logDampedPower, log_exp]
  congr 1
  field_simp

/-- The same margin also puts the original kernel on its decreasing tail. -/
theorem logDampedPower_nu_turn_le {q ν X : ℝ} (hX : 0 < X) (hν : 0 < ν)
    (hmargin : 1 < (q - 1) * ν ^ 2) :
    exp (sqrt (X ^ 2 / q)) ≤ exp (ν * X) := by
  have hp := logDampedPower_nu_exponent_mem hν hmargin
  have hd : 0 < q - (q - 1 / ν ^ 2) := sub_pos.mpr hp.2
  have hle : q - (q - 1 / ν ^ 2) ≤ q := by linarith [hp.1]
  exact (exp_le_exp.mpr (sqrt_le_sqrt
    (div_le_div_of_nonneg_left (sq_nonneg X) hd hle))).trans
      (logDampedPower_nu_cutoff hX hν hmargin)

/-- The integral factor after choosing the Rosser exponent and cancelling all split powers. -/
def logDampedNuIntegralFactor (q ν X b : ℝ) : ℝ :=
  (exp (ν * X) / b) *
    ((ν * X - log b) / (q - 1 / ν ^ 2 - 1) + 1 / (q - 1 / ν ^ 2 - 1) ^ 2) +
    1 / (q - 1 / ν ^ 2)

/-- The full density majorant reduces exactly to one kernel exponential and a scalar factor. -/
theorem logDampedPowerMajorant_nu_mul_integralFactor {q ν X b : ℝ}
    (hX : 0 < X) (hν : 0 < ν) (hb : 0 < b) (hmargin : 1 < (q - 1) * ν ^ 2) :
    logDampedPowerMajorant (X ^ 2) q (q - 1 / ν ^ 2) (exp (ν * X)) *
        logDampedPowerIntegralFactor (q - 1 / ν ^ 2) b (exp (ν * X)) =
      exp (-q * (ν * X) - X / ν) * logDampedNuIntegralFactor q ν X b := by
  rw [logDampedPowerMajorant, ite_eq_left (logDampedPower_nu_cutoff hX hν hmargin),
    logDampedPower_mul_integralFactor (exp_pos _), logDampedPower_nu hX hν,
    log_div (exp_pos _).ne' hb.ne', log_exp]
  rfl

/-- The parameterized integral factor is positive above the density scale. -/
theorem logDampedNuIntegralFactor_pos {q ν X b : ℝ}
    (hν : 0 < ν) (hb : 0 < b) (hmargin : 1 < (q - 1) * ν ^ 2)
    (hbu : b ≤ exp (ν * X)) : 0 < logDampedNuIntegralFactor q ν X b := by
  have hp := logDampedPower_nu_exponent_mem hν hmargin
  have hp0 : 0 < q - 1 / ν ^ 2 := lt_trans zero_lt_one hp.1
  have hd : 0 < q - 1 / ν ^ 2 - 1 := sub_pos.mpr hp.1
  have hl : 0 ≤ ν * X - log b := by
    simpa only [log_exp] using sub_nonneg.mpr (log_le_log hb hbu)
  unfold logDampedNuIntegralFactor
  positivity

/-- The inverse-parameter decay splits into the three exponential factors used by Rosser. -/
theorem exp_neg_div_eq_mul_exp_square {X ν : ℝ} (hν : 0 < ν) :
    exp (-X / ν) = exp (ν * X) * exp (-2 * X) * exp (-X * (1 - ν) ^ 2 / ν) := by
  rw [← exp_add, ← exp_add]
  congr 1
  field_simp
  ring

end

end Real
