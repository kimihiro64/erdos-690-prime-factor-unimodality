import PrimeFactorUnimodality.Helpers.Analytic.XiAffinePhase

/-! # Shared affine phase, quadratic remainder and retained Gamma-error regressions -/

set_option autoImplicit false

namespace PrimeFactorUnimodality.Tests

example {base t : ℝ} (hb : 0 < base) (ht : 0 < t) :
    xiSimplePhase t - xiAffinePhase base t =
      (t * Real.log (t / base) - (t - base)) / 2 :=
  xiSimplePhase_sub_affine_eq hb ht

example {base t : ℝ} (hb : 0 < base) (ht : 0 < t) :
    xiAffinePhase base t ≤ xiSimplePhase t := xiAffinePhase_le_simple hb ht

example {base t : ℝ} (hb : 0 < base) (ht : 0 < t) :
    |xiSimplePhase t - xiAffinePhase base t| ≤ (t - base) ^ 2 / (2 * base) :=
  abs_xiSimplePhase_sub_affine_le hb ht

example {base t : ℝ} (hb : 0 < base) (ht : 0 < t) :
    |turingStirlingPhase t - xiAffinePhase base t| ≤
      33 / (16 * t) + (t - base) ^ 2 / (2 * base) :=
  abs_turingStirlingPhase_sub_affine_le hb ht

example {base t : ℝ} (hb : 0 < base) (ht : 0 < t) :
    |turingCountingPhase t - xiAffinePhase base t| ≤
      1 / 10 + 33 / (16 * t) + (t - base) ^ 2 / (2 * base) :=
  abs_turingCountingPhase_sub_affine_le hb ht

example (base : ℝ) : xiAffinePhase base base = xiSimplePhase base := by
  simp [xiAffinePhase]

example {base : ℝ} (hb : 0 < base) :
    |xiSimplePhase base - xiAffinePhase base base| ≤ 0 := by
  simpa using abs_xiSimplePhase_sub_affine_le hb hb

example {t : ℝ} (ht : |t - 170000000| ≤ 10) :
    |xiSimplePhase t - xiAffinePhase 170000000 t| ≤ 1 / 3000000 := by
  have htpos : 0 < t := by have := (abs_le.mp ht).1; linarith
  apply (abs_xiSimplePhase_sub_affine_le (by norm_num) htpos).trans
  have hs : (t - 170000000) ^ 2 ≤ (10 : ℝ) ^ 2 := by
    simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg (t - 170000000)) ht 2
  calc
    _ ≤ (10 : ℝ) ^ 2 / (2 * 170000000) := div_le_div_of_nonneg_right hs (by norm_num)
    _ ≤ 1 / 3000000 := by norm_num

end PrimeFactorUnimodality.Tests
