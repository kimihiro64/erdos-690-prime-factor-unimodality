/-
Copyright (c) 2026 Jonas Whidden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonas Whidden
-/
import PrimeFactorUnimodality.Mathlib.Analysis.SpecialFunctions.Integrals.LogDamped
import PrimeFactorUnimodality.Mathlib.Analysis.SpecialFunctions.Integrals.LogPowerTail
import PrimeFactorUnimodality.Mathlib.Analysis.SpecialFunctions.Pow.LogDampedMajorant

/-! # Closed-form bounds for logarithmically weighted damped tails

The free power exponent separates exponential damping from exactly
integrable power tails. The density and reciprocal-height correction
are controlled together, without leaving an improper integral in the bound.
-/

namespace Real

noncomputable section

open MeasureTheory Set

/-- The elementary integral factor for the logarithmic density and height correction. -/
def logDampedPowerIntegralFactor (p b u : ℝ) : ℝ :=
  (1 / b) * u ^ (1 - p) * (log (u / b) / (p - 1) + 1 / (p - 1) ^ 2) + u ^ (-p) / p

/-- The extra reciprocal height makes a positive inverse power integrable. -/
theorem integrableOn_rpow_div_tail {p u : ℝ} (hp : 0 < p) (hu : 0 < u) :
    IntegrableOn (fun t : ℝ => t ^ (-p) / t) (Ioi u) := by
  apply (integrableOn_Ioi_rpow_of_lt (by linarith : -p - 1 < -1) hu).congr_fun
    _ measurableSet_Ioi
  intro t ht
  dsimp only
  rw [rpow_sub (hu.trans ht), rpow_one]

/-- The reciprocal-height power integral is evaluated exactly. -/
theorem integral_rpow_div_tail {p u : ℝ} (hp : 0 < p) (hu : 0 < u) :
    (∫ t : ℝ in Ioi u, t ^ (-p) / t) = u ^ (-p) / p := by
  calc
    _ = ∫ t : ℝ in Ioi u, t ^ (-p - 1) := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro t ht
      dsimp only
      rw [rpow_sub (hu.trans ht), rpow_one]
    _ = _ := by
      rw [integral_Ioi_rpow_of_lt (by linarith : -p - 1 < -1) hu,
        show -p - 1 + 1 = -p by ring]
      ring

/-- The scaled logarithmic power density is integrable for every positive scale. -/
theorem integrableOn_log_density_rpow {p b u : ℝ}
    (hp : 1 < p) (hb : 0 < b) (hu : 0 < u) :
    IntegrableOn (fun t => ((1 / b) * log (t / b)) * t ^ (-p)) (Ioi u) := by
  have hi : IntegrableOn (fun t => (1 / b) * ((log t - log b) * t ^ (-p))) (Ioi u) :=
    (integrableOn_log_sub_mul_rpow_tail hp hu (log b)).const_mul (1 / b)
  apply hi.congr_fun _ measurableSet_Ioi
  intro t ht
  dsimp only
  rw [log_div (hu.trans ht).ne' hb.ne']
  ring

/-- The complete two-term power majorant has an elementary value. -/
theorem integral_log_density_rpow_add_div {p b u : ℝ}
    (hp : 1 < p) (hb : 0 < b) (hu : 0 < u) :
    (∫ t in Ioi u, ((1 / b) * log (t / b)) * t ^ (-p)) +
        (∫ t in Ioi u, t ^ (-p) / t) = logDampedPowerIntegralFactor p b u := by
  have he : (∫ t in Ioi u, ((1 / b) * log (t / b)) * t ^ (-p)) =
      (1 / b) * ∫ t in Ioi u, (log t - log b) * t ^ (-p) := by
    rw [← integral_const_mul]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro t ht
    dsimp only
    rw [log_div (hu.trans ht).ne' hb.ne']
    ring
  rw [he, integral_log_sub_mul_rpow_tail hp hu,
    integral_rpow_div_tail (by linarith : 0 < p) hu]
  unfold logDampedPowerIntegralFactor
  rw [log_div hu.ne' hb.ne']
  ring

/-- A power majorant gives a closed bound on the actual damped density integrals. -/
theorem integral_logDampedPower_density_le_of_majorant {a q p b u C : ℝ}
    (ha : 0 ≤ a) (hq : 2 ≤ q) (hp : 1 < p) (hb : 0 < b) (hu : 1 < u) (hbu : b ≤ u)
    (hbound : ∀ t ∈ Ici u, logDampedPower a q t ≤ t ^ (-p) * C) :
    (∫ t in Ioi u, ((1 / b) * log (t / b)) * logDampedPower a q t) +
        (∫ t in Ioi u, logDampedPower a q t / t) ≤
      C * logDampedPowerIntegralFactor p b u := by
  have hu0 : 0 < u := lt_trans zero_lt_one hu
  have hf : IntegrableOn (fun t => ((1 / b) * log (t / b)) * logDampedPower a q t) (Ioi u) := by
    have hi : IntegrableOn (fun t => (1 / b) * (log (t / b) * logDampedPower a q t)) (Ioi u) :=
      (integrableOn_log_div_mul_logDampedPower ha hq hu hb).const_mul (1 / b)
    apply hi.congr_fun _ measurableSet_Ioi
    intro t _
    dsimp
    ring
  have hD : (∫ t in Ioi u, ((1 / b) * log (t / b)) * logDampedPower a q t) ≤
      C * ∫ t in Ioi u, ((1 / b) * log (t / b)) * t ^ (-p) := by
    rw [← integral_const_mul]
    apply integral_mono_ae hf ((integrableOn_log_density_rpow hp hb hu0).const_mul C)
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have ht' : u < t := ht
    have hl : 0 ≤ (1 / b) * log (t / b) := mul_nonneg (by positivity)
      (log_nonneg ((le_div_iff₀ hb).mpr (by simpa only [one_mul] using hbu.trans ht'.le)))
    convert mul_le_mul_of_nonneg_left (hbound t (mem_Ici.mpr ht'.le)) hl using 1
    ring
  have hE : (∫ t in Ioi u, logDampedPower a q t / t) ≤
      C * ∫ t in Ioi u, t ^ (-p) / t := by
    rw [← integral_const_mul]
    apply integral_mono_ae (integrableOn_logDampedPower_div ha hq hu)
      ((integrableOn_rpow_div_tail (by linarith : 0 < p) hu0).const_mul C)
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have ht' : u < t := ht
    convert div_le_div_of_nonneg_right (hbound t (mem_Ici.mpr ht'.le)) (hu0.trans ht').le using 1
    ring
  calc
    _ ≤ C * (∫ t in Ioi u, ((1 / b) * log (t / b)) * t ^ (-p)) +
        C * (∫ t in Ioi u, t ^ (-p) / t) := add_le_add hD hE
    _ = _ := by rw [← mul_add, integral_log_density_rpow_add_div hp hb hu0]

/-- In the cutoff branch, the split power cancels exactly against the integral factor. -/
theorem logDampedPower_mul_integralFactor {a q p b u : ℝ} (hu : 0 < u) :
    logDampedPower a (q - p) u * logDampedPowerIntegralFactor p b u =
      logDampedPower a q u *
        ((u / b) * (log (u / b) / (p - 1) + 1 / (p - 1) ^ 2) + 1 / p) := by
  have hr : u ^ (1 - p) = u * u ^ (-p) := by
    rw [show 1 - p = 1 + -p by ring, rpow_add hu, rpow_one]
  rw [logDampedPower_split (a := a) (q := q) (p := p) hu]
  unfold logDampedPowerIntegralFactor
  rw [hr]
  ring

/-- The majorant factor is nonnegative beyond the logarithm scale. -/
theorem logDampedPowerIntegralFactor_nonneg {p b u : ℝ}
    (hp : 1 < p) (hb : 0 < b) (hbu : b ≤ u) : 0 ≤ logDampedPowerIntegralFactor p b u := by
  have hu : 0 < u := hb.trans_le hbu
  have hlog : 0 ≤ log (u / b) := log_nonneg ((le_div_iff₀ hb).mpr (by simpa using hbu))
  have hp0 : 0 < p := lt_trans zero_lt_one hp
  have hp1 : 0 < p - 1 := sub_pos.mpr hp
  unfold logDampedPowerIntegralFactor
  positivity

end

end Real
