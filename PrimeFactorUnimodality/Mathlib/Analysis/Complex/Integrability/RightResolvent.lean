/-
Copyright (c) 2026 Jonas Whidden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonas Whidden
-/
import PrimeFactorUnimodality.Mathlib.Analysis.Complex.Integrability.Resolvent

/-! # Absolute pairing with poles to the right of a vertical contour

Reflection of the height and the complex argument reduces the right-pole
Laplace representation to the left-pole Fubini theorem. The resulting
height transform has positive rather than negative frequency.
-/

namespace Complex

noncomputable section

open MeasureTheory

/-- A pole strictly right of the contour also preserves integrability of the weight. -/
theorem integrable_div_vertical_of_right {H : ℝ → ℂ} (hH : Integrable H)
    {c : ℝ} {ρ : ℂ} (hρ : c < ρ.re) :
    Integrable (fun t : ℝ => H t / ((c : ℂ) + (t : ℂ) * I - ρ)) := by
  have hm : AEStronglyMeasurable (fun t : ℝ => H t / ((c : ℂ) + (t : ℂ) * I - ρ)) volume := by
    simp only [div_eq_mul_inv]
    exact hH.aestronglyMeasurable.fun_mul (by fun_prop)
  apply (hH.norm.div_const (ρ.re - c)).mono' hm
  filter_upwards with t
  have hden : ρ.re - c ≤ ‖(c : ℂ) + (t : ℂ) * I - ρ‖ := by
    simpa only [sub_re, add_re, ofReal_re, mul_re, I_re, I_im, ofReal_im,
      mul_zero, zero_mul, sub_zero, add_zero, norm_sub_rev ρ] using
      re_le_norm (ρ - ((c : ℂ) + (t : ℂ) * I))
  rw [norm_div]
  exact div_le_div_of_nonneg_left (norm_nonneg _) (sub_pos.mpr hρ) hden

/-- The right-pole representation pairs the positive-frequency transform with a decaying kernel. -/
theorem integral_div_rev_vertical_eq_integral_exp {H : ℝ → ℂ}
    (hH : Integrable H) (hcont : Continuous H) {c : ℝ} {ρ : ℂ} (hρ : c < ρ.re) :
    (∫ t : ℝ, H t / (ρ - ((c : ℂ) + (t : ℂ) * I))) =
      ∫ u : ℝ in Set.Ioi 0, exp (-(ρ - c) * (u : ℂ)) *
        (∫ t : ℝ, exp ((t : ℂ) * I * (u : ℂ)) * H t) := by
  have hleft := integral_div_vertical_eq_integral_exp hH.comp_neg
    (hcont.comp continuous_neg) (c := -c) (ρ := -ρ) (by simp only [neg_re]; linarith)
  have hden (t : ℝ) : ((-c : ℝ) : ℂ) + (t : ℂ) * I - -ρ =
      ρ - ((c : ℂ) + ((-t : ℝ) : ℂ) * I) := by push_cast; ring
  simp_rw [hden] at hleft
  have hflip := (Measure.measurePreserving_neg (volume : Measure ℝ)).integral_comp
    (Homeomorph.neg ℝ).measurableEmbedding
    (fun t : ℝ => H t / (ρ - ((c : ℂ) + (t : ℂ) * I)))
  rw [hflip] at hleft
  rw [hleft]
  apply integral_congr_ae
  filter_upwards with u
  have harg : ((-c : ℝ) : ℂ) - -ρ = ρ - c := by push_cast; ring
  rw [harg]
  congr 1
  simpa only [ofReal_neg, neg_mul] using
    (Measure.measurePreserving_neg (volume : Measure ℝ)).integral_comp
      (Homeomorph.neg ℝ).measurableEmbedding
      (fun t : ℝ => exp ((t : ℂ) * I * (u : ℂ)) * H t)

end

end Complex
