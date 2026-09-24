import PrimeFactorUnimodality.Helpers.Analytic.XiSimplePhase

/-! # A shared affine phase with a quadratic remainder

An expansion at one positive base height uses only that base's logarithm.
The elementary inequality `log u ≤ u - 1`, applied in both directions,
gives a nonnegative remainder bounded by a quadratic. All heights in a
block can therefore reuse one affine model. The Stirling simplification
error and the separate Gamma error are retained in the final bounds.
-/

namespace PrimeFactorUnimodality

noncomputable section

/-- The tangent slope of the elementary xi phase at a positive height. -/
def xiSimplePhaseSlope (base : ℝ) : ℝ :=
  (Real.log (base / 2) - Real.log Real.pi) / 2

/-- One affine model shared by every endpoint in a block. -/
def xiAffinePhase (base t : ℝ) : ℝ :=
  xiSimplePhase base + xiSimplePhaseSlope base * (t - base)

/-- Cancellation leaves just a relative logarithm in the exact affine remainder. -/
theorem xiSimplePhase_sub_affine_eq {base t : ℝ} (hb : 0 < base) (ht : 0 < t) :
    xiSimplePhase t - xiAffinePhase base t =
      (t * Real.log (t / base) - (t - base)) / 2 := by
  unfold xiAffinePhase xiSimplePhaseSlope xiSimplePhase
  rw [Real.log_div ht.ne' (by norm_num : (2 : ℝ) ≠ 0),
    Real.log_div hb.ne' (by norm_num : (2 : ℝ) ≠ 0), Real.log_div ht.ne' hb.ne']
  ring

/-- The shared affine model underestimates the elementary phase at every positive height. -/
theorem xiAffinePhase_le_simple {base t : ℝ} (hb : 0 < base) (ht : 0 < t) :
    xiAffinePhase base t ≤ xiSimplePhase t := by
  have hlog := Real.log_le_sub_one_of_pos (div_pos hb ht)
  have h := mul_le_mul_of_nonneg_left hlog ht.le
  have he : t * (base / t - 1) = base - t := by
    field_simp
  rw [he, Real.log_div hb.ne' ht.ne'] at h
  have hid := xiSimplePhase_sub_affine_eq hb ht
  rw [Real.log_div ht.ne' hb.ne'] at hid
  nlinarith

/-- A single quadratic budget bounds the remainder, with no logarithm at the sample height. -/
theorem xiSimplePhase_sub_affine_le {base t : ℝ} (hb : 0 < base) (ht : 0 < t) :
    xiSimplePhase t - xiAffinePhase base t ≤ (t - base) ^ 2 / (2 * base) := by
  have h := mul_le_mul_of_nonneg_left (Real.log_le_sub_one_of_pos (div_pos ht hb)) ht.le
  rw [xiSimplePhase_sub_affine_eq hb ht]
  have he : (t * (t / base - 1) - (t - base)) / 2 =
      (t - base) ^ 2 / (2 * base) := by
    field_simp
  rw [← he]
  linarith

/-- The absolute remainder is the same nonnegative quadratic-bounded quantity. -/
theorem abs_xiSimplePhase_sub_affine_le {base t : ℝ} (hb : 0 < base) (ht : 0 < t) :
    |xiSimplePhase t - xiAffinePhase base t| ≤ (t - base) ^ 2 / (2 * base) := by
  rw [abs_of_nonneg (sub_nonneg.mpr (xiAffinePhase_le_simple hb ht))]
  exact xiSimplePhase_sub_affine_le hb ht

/-- Include the full argument and logarithmic-norm simplification error. -/
theorem abs_turingStirlingPhase_sub_affine_le {base t : ℝ} (hb : 0 < base) (ht : 0 < t) :
    |turingStirlingPhase t - xiAffinePhase base t| ≤
      33 / (16 * t) + (t - base) ^ 2 / (2 * base) :=
  (abs_sub_le _ _ _).trans (add_le_add (abs_turingStirlingPhase_sub_simple_le ht)
    (abs_xiSimplePhase_sub_affine_le hb ht))

/-- The actual counting phase still carries its separate one-tenth Gamma remainder. -/
theorem abs_turingCountingPhase_sub_affine_le {base t : ℝ} (hb : 0 < base) (ht : 0 < t) :
    |turingCountingPhase t - xiAffinePhase base t| ≤
      1 / 10 + 33 / (16 * t) + (t - base) ^ 2 / (2 * base) := by
  have h := (abs_sub_le (turingCountingPhase t) (turingStirlingPhase t)
    (xiAffinePhase base t)).trans (add_le_add (abs_turingCountingPhase_sub_stirling_le t)
      (abs_turingStirlingPhase_sub_affine_le hb ht))
  simpa only [add_assoc] using h

end

end PrimeFactorUnimodality
