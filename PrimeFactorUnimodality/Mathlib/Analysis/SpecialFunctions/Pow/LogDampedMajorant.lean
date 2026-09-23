/-
Copyright (c) 2026 Jonas Whidden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonas Whidden
-/
import PrimeFactorUnimodality.Mathlib.Analysis.SpecialFunctions.Pow.LogDampedShape

/-! # Integrable power majorants for inverse-logarithmically damped powers

Splitting off an arbitrary real power leaves a damped kernel controlled
by its global peak or, after its turning point, its value at the cutoff.
The power parameter remains free for quantitative optimization.
-/

namespace Real

noncomputable section

open Set

/-- Split off any real power, keeping the remaining damping exact. -/
theorem logDampedPower_split {a q p t : ℝ} (ht : 0 < t) :
    logDampedPower a q t = t ^ (-p) * logDampedPower a (q - p) t := by
  unfold logDampedPower
  rw [Real.rpow_def_of_pos ht, ← Real.exp_add]
  congr 1
  ring

/-- The global peak bounds the remaining kernel for every height above one. -/
theorem logDampedPower_le_rpow_mul_peak {a q p t : ℝ}
    (ha : 0 ≤ a) (hpq : p ≤ q) (ht : 1 < t) :
    logDampedPower a q t ≤ t ^ (-p) * exp (-2 * sqrt (a * (q - p))) := by
  rw [logDampedPower_split (p := p) (lt_trans zero_lt_one ht)]
  exact mul_le_mul_of_nonneg_left
    (logDampedPower_le_exp_sqrt ha (sub_nonneg.mpr hpq) ht)
    (rpow_nonneg (lt_trans zero_lt_one ht).le _)

/-- After the remaining kernel's turning point, its cutoff value gives a sharper majorant. -/
theorem logDampedPower_le_rpow_mul_cutoff {a q p u t : ℝ}
    (ha : 0 ≤ a) (hpq : p < q) (hu : 1 < u) (hut : u ≤ t)
    (hw : exp (sqrt (a / (q - p))) ≤ u) :
    logDampedPower a q t ≤ t ^ (-p) * logDampedPower a (q - p) u := by
  have hm : AntitoneOn (logDampedPower a (q - p)) (Ici u) := by
    apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Ici u)
      (continuousOn_logDampedPower (fun t ht => hu.trans_le ht))
      (fun t ht => (hasDerivAt_logDampedPower
        (hu.trans_le (interior_subset ht))).hasDerivWithinAt)
    intro t ht
    exact logDampedPowerSlope_nonpos_after ha (sub_pos.mpr hpq)
      (hu.trans_le (interior_subset ht)) (hw.trans (interior_subset ht))
  rw [logDampedPower_split (p := p) (lt_trans zero_lt_one (hu.trans_le hut))]
  exact mul_le_mul_of_nonneg_left (hm self_mem_Ici (mem_Ici.mpr hut) hut)
    (rpow_nonneg (lt_trans zero_lt_one (hu.trans_le hut)).le _)

/-- Use the cutoff value after the remaining turning point, and its global peak otherwise. -/
def logDampedPowerMajorant (a q p u : ℝ) : ℝ :=
  if exp (sqrt (a / (q - p))) ≤ u then logDampedPower a (q - p) u
  else exp (-2 * sqrt (a * (q - p)))

/-- Both branches of the selected coefficient are strictly positive. -/
theorem logDampedPowerMajorant_pos (a q p u : ℝ) : 0 < logDampedPowerMajorant a q p u := by
  unfold logDampedPowerMajorant
  split_ifs
  · exact logDampedPower_pos _ _ _
  · exact exp_pos _

/-- Selection preserves the global peak bound, including equality of the split exponents. -/
theorem logDampedPowerMajorant_le_peak {a q p u : ℝ}
    (ha : 0 ≤ a) (hpq : p ≤ q) (hu : 1 < u) :
    logDampedPowerMajorant a q p u ≤ exp (-2 * sqrt (a * (q - p))) := by
  unfold logDampedPowerMajorant
  split_ifs
  · exact logDampedPower_le_exp_sqrt ha (sub_nonneg.mpr hpq) hu
  · exact le_rfl

/-- The selected coefficient majorizes the kernel on the entire closed tail. -/
theorem logDampedPower_le_rpow_mul_majorant {a q p u t : ℝ}
    (ha : 0 ≤ a) (hpq : p < q) (hu : 1 < u) (hut : u ≤ t) :
    logDampedPower a q t ≤ t ^ (-p) * logDampedPowerMajorant a q p u := by
  unfold logDampedPowerMajorant
  split_ifs with hw
  · exact logDampedPower_le_rpow_mul_cutoff ha hpq hu hut hw
  · exact logDampedPower_le_rpow_mul_peak ha hpq.le (hu.trans_le hut)

end

end Real
