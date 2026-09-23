/-
Copyright (c) 2026 Jonas Whidden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonas Whidden
-/
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! # Exact logarithmic power-tail integrals

For every real exponent above one and positive cutoff, the logarithmic
power tail has an elementary primitive. Arbitrary logarithmic offsets
are permitted, even when the integrand changes sign.
-/

namespace Real

open Filter MeasureTheory Set
open scoped Topology

/-- An elementary primitive for a logarithmically weighted inverse power. -/
noncomputable def logPowerTailPrimitive (p c t : ℝ) : ℝ :=
  -(t ^ (1 - p)) * ((log t - c) / (p - 1) + 1 / (p - 1) ^ 2)

/-- The primitive differentiates to the full logarithmic power kernel. -/
theorem hasDerivAt_logPowerTailPrimitive {p c t : ℝ} (hp : 1 < p) (ht : 0 < t) :
    HasDerivAt (logPowerTailPrimitive p c) ((log t - c) * t ^ (-p)) t := by
  have hd := ((hasDerivAt_rpow_const (p := 1 - p) (Or.inl ht.ne')).neg).mul
    ((((hasDerivAt_log ht.ne').sub_const c).div_const (p - 1)).add_const (1 / (p - 1) ^ 2))
  have he : t ^ (1 - p) = t ^ (-p) * t := by
    rw [show 1 - p = -p + 1 by ring, rpow_add ht, rpow_one]
  convert hd using 1
  · funext t
    rfl
  · dsimp
    rw [show 1 - p - 1 = -p by ring, he]
    field_simp [ht.ne', (sub_pos.mpr hp).ne']
    ring

/-- Logarithmic growth is dominated by every positive power. -/
theorem tendsto_logPowerTailPrimitive (c : ℝ) {p : ℝ} (hp : 1 < p) :
    Tendsto (logPowerTailPrimitive p c) atTop (𝓝 0) := by
  have hL := (isLittleO_log_rpow_atTop (sub_pos.mpr hp)).tendsto_div_nhds_zero
  have hP : Tendsto (fun t : ℝ => t ^ (1 - p)) atTop (𝓝 0) := by
    simpa only [neg_sub] using tendsto_rpow_neg_atTop (sub_pos.mpr hp)
  have hn := ((hL.div_const (p - 1)).neg).add (hP.const_mul (c / (p - 1) - 1 / (p - 1) ^ 2))
  simp only [zero_div, neg_zero, mul_zero, add_zero] at hn
  apply hn.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
  have he : t ^ (1 - p) = (t ^ (p - 1))⁻¹ := by
    rw [show 1 - p = -(p - 1) by ring, rpow_neg ht.le]
  dsimp [logPowerTailPrimitive]
  rw [he]
  ring

/-- The tail is absolutely integrable for every real logarithmic offset. -/
theorem integrableOn_log_sub_mul_rpow_tail {p u : ℝ} (hp : 1 < p) (hu : 0 < u) (c : ℝ) :
    IntegrableOn (fun t => (log t - c) * t ^ (-p)) (Ioi u) := by
  have hb : IntegrableOn (fun t => (log t - log u) * t ^ (-p)) (Ioi u) := by
    apply integrableOn_Ioi_deriv_of_nonneg'
      (fun t ht => hasDerivAt_logPowerTailPrimitive hp (hu.trans_le ht)) _
      (tendsto_logPowerTailPrimitive (log u) hp)
    intro t ht
    exact mul_nonneg (sub_nonneg.mpr (log_le_log hu ht.le))
      (rpow_nonneg (hu.trans ht).le _)
  have hc := (integrableOn_Ioi_rpow_of_lt (by linarith : -p < -1) hu).const_mul (log u - c)
  apply (hb.add hc).congr_fun _ measurableSet_Ioi
  intro t _
  dsimp
  ring

/-- The complete logarithmic power tail equals its elementary endpoint expression. -/
theorem integral_log_sub_mul_rpow_tail {p u : ℝ} (hp : 1 < p) (hu : 0 < u) (c : ℝ) :
    (∫ t in Ioi u, (log t - c) * t ^ (-p)) =
      u ^ (1 - p) * ((log u - c) / (p - 1) + 1 / (p - 1) ^ 2) := by
  have he := integral_Ioi_of_hasDerivAt_of_tendsto'
    (fun t ht => hasDerivAt_logPowerTailPrimitive hp (hu.trans_le ht))
    (integrableOn_log_sub_mul_rpow_tail hp hu c) (tendsto_logPowerTailPrimitive c hp)
  simpa [logPowerTailPrimitive] using he

end Real
