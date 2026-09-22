/-
Copyright (c) 2026 Jonas Whidden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonas Whidden
-/
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! # Inverse-square imaginary parts of a summable complex family

On a bounded vertical strip separated from the real axis, inverse-square
imaginary parts are dominated by inverse-square norms. This transfers an
existing summability result without enumerating the family or assuming
that its real parts agree.
-/

namespace Real

/-- An absolute-height cutoff implies separation from the evaluation height. -/
theorem sq_le_sub_sq_of_abs_cutoff {t γ H : ℝ} (hH : 0 ≤ H)
    (hcut : |t| + H ≤ |γ|) : H ^ 2 ≤ (t - γ) ^ 2 := by
  have htri : |γ| ≤ |t| + |t - γ| := by
    simpa [abs_sub_comm] using abs_add_le t (γ - t)
  have hdist : H ≤ |t - γ| := by linarith
  nlinarith [sq_abs (t - γ), mul_nonneg (sub_nonneg.mpr hdist)
    (add_nonneg (abs_nonneg (t - γ)) hH)]

end Real

namespace Complex

noncomputable section

/-- Explicit comparison on a bounded strip away from the real axis. -/
theorem inv_im_sq_le_mul_inv_norm_sq {z : ℂ} {B H : ℝ}
    (hH : 0 < H) (hre : |z.re| ≤ B) (him : H ^ 2 ≤ z.im ^ 2) :
    1 / z.im ^ 2 ≤ (1 + B ^ 2 / H ^ 2) * ‖z‖⁻¹ ^ 2 := by
  have hH₂ : 0 < H ^ 2 := sq_pos_of_pos hH
  have him₂ : 0 < z.im ^ 2 := hH₂.trans_le him
  have hnorm : ‖z‖ ^ 2 = z.re ^ 2 + z.im ^ 2 := by
    rw [← normSq_eq_norm_sq, normSq_apply]
    ring
  have hn : 0 < ‖z‖ ^ 2 := by rw [hnorm]; positivity
  have hre₂ : z.re ^ 2 ≤ B ^ 2 := by
    obtain ⟨hl, hu⟩ := abs_le.mp hre
    nlinarith [mul_nonneg (sub_nonneg.mpr hu) (by linarith : 0 ≤ B + z.re)]
  have hratio : 1 ≤ z.im ^ 2 / H ^ 2 := (le_div_iff₀ hH₂).mpr (by simpa using him)
  have hb : B ^ 2 ≤ B ^ 2 / H ^ 2 * z.im ^ 2 := by
    convert mul_le_mul_of_nonneg_left hratio (sq_nonneg B) using 1 <;> ring
  rw [inv_pow, ← div_eq_mul_inv]
  apply (div_le_div_iff₀ him₂ hn).mpr
  rw [hnorm]
  nlinarith only [hre₂, hb]

/-- Inverse-square norm summability implies imaginary-part summability on a separated strip. -/
theorem summable_inv_im_sq_of_norm_inv_sq {ι : Type*} {z : ι → ℂ} {B H : ℝ}
    (hsum : Summable (fun i => ‖z i‖⁻¹ ^ 2)) (hH : 0 < H)
    (hre : ∀ i, |(z i).re| ≤ B) (him : ∀ i, H ^ 2 ≤ (z i).im ^ 2) :
    Summable (fun i => 1 / (z i).im ^ 2) := by
  apply (hsum.mul_left (1 + B ^ 2 / H ^ 2)).of_norm_bounded
  intro i
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity : 0 ≤ 1 / (z i).im ^ 2)]
  exact inv_im_sq_le_mul_inv_norm_sq hH (hre i) (him i)

end

end Complex
