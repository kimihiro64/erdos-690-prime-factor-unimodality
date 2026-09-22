/-
Copyright (c) 2026 Jonas Whidden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonas Whidden
-/
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith

/-! # Logarithmic ratios under a positive affine change

For `a ≥ 1` and `b ≥ 0`, the ratio `log x / log (a*x+b)` increases on
`x > 1` and is at most one. The proof compares `a*x+b` with
`(a+b/T)*x` and uses monotonicity of the logarithm, without differentiation.
-/

namespace Real

/-- The logarithmic ratio at the left endpoint bounds every later height from below. -/
theorem log_div_log_affine_le {a b T t : ℝ} (ha : 1 ≤ a) (hb : 0 ≤ b)
    (hT : 1 < T) (hTt : T ≤ t) :
    log T / log (a * T + b) ≤ log t / log (a * t + b) := by
  have hTpos : 0 < T := by linarith
  have htpos : 0 < t := hTpos.trans_le hTt
  have hc : 1 ≤ a + b / T := ha.trans (le_add_of_nonneg_right (div_nonneg hb hTpos.le))
  have hcpos : 0 < a + b / T := by linarith
  have hmul : (a + b / T) * T = a * T + b := by field_simp
  have hbound : a * t + b ≤ (a + b / T) * t := by
    have h := mul_le_mul_of_nonneg_left hTt (div_nonneg hb hTpos.le)
    have hcancel : b / T * T = b := div_mul_cancel₀ b hTpos.ne'
    rw [hcancel] at h
    nlinarith only [h]
  have hbase : T ≤ a * T + b := by nlinarith only [ha, hb, hTpos]
  have hlater : t ≤ a * t + b := by nlinarith only [ha, hb, htpos]
  have hlogT : 0 < log T := log_pos hT
  have hlogAT : 0 < log (a * T + b) := log_pos (hT.trans_le hbase)
  have hlogAt : 0 < log (a * t + b) := log_pos ((hT.trans_le hTt).trans_le hlater)
  have hlogmono : log T ≤ log t := log_le_log hTpos hTt
  have hlogc : 0 ≤ log (a + b / T) := log_nonneg hc
  have hlogbound : log (a * t + b) ≤ log (a + b / T) + log t := by
    rw [← log_mul hcpos.ne' htpos.ne']
    exact log_le_log (htpos.trans_le hlater) hbound
  have hlogbase : log (a * T + b) = log (a + b / T) + log T := by
    rw [← log_mul hcpos.ne' hTpos.ne', hmul]
  apply (div_le_div_iff₀ hlogAT hlogAt).mpr
  rw [hlogbase]
  nlinarith only [mul_le_mul_of_nonneg_left hlogbound hlogT.le,
    mul_le_mul_of_nonneg_left hlogmono hlogc]

/-- The affine logarithmic ratio is monotone throughout its natural domain. -/
theorem monotoneOn_log_div_log_affine {a b : ℝ} (ha : 1 ≤ a) (hb : 0 ≤ b) :
    MonotoneOn (fun t : ℝ => log t / log (a * t + b)) (Set.Ioi 1) := by
  intro T hT t _ hTt
  exact log_div_log_affine_le ha hb hT hTt

/-- Enlarging a positive height by this affine change makes its logarithmic ratio at most one. -/
theorem log_div_log_affine_le_one {a b t : ℝ} (ha : 1 ≤ a) (hb : 0 ≤ b) (ht : 1 < t) :
    log t / log (a * t + b) ≤ 1 := by
  have hbase : t ≤ a * t + b := by nlinarith only [ha, hb, ht]
  exact (div_le_one (log_pos (ht.trans_le hbase))).mpr (log_le_log (by linarith) hbase)

end Real
