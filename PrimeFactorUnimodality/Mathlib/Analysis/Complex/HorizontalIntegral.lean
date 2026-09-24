/-
Copyright (c) 2026 Jonas Whidden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonas Whidden
-/
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-! # Moving an absolutely convergent integral across a horizontal strip

Cauchy-Goursat on finite rectangles gives equality of the full horizontal
integrals when both connecting edges vanish. The edge hypotheses are limits
of actual integrals, with no assertion about residues in a nonholomorphic strip.
-/

open MeasureTheory Filter Set
open scoped Topology

namespace Complex

/-- A uniform bound tending to zero makes the whole connecting edge vanish. -/
theorem tendsto_integral_vertical_zero_of_bound {f : ℝ → ℝ → ℂ} {c : ℝ}
    {l : Filter ℝ} {B : ℝ → ℝ} (hB : Tendsto B l (𝓝 0))
    (hb : ∀ᶠ T in l, ∀ y ∈ uIcc 0 c, ‖f T y‖ ≤ B T) :
    Tendsto (fun T => ∫ y in (0 : ℝ)..c, f T y) l (𝓝 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  apply squeeze_zero' (Eventually.of_forall (fun _ => norm_nonneg _)) ?_
    (by simpa using hB.mul_const |c|)
  filter_upwards [hb] with T hT
  simpa using intervalIntegral.norm_integral_le_of_norm_le_const
    (fun y hy => hT y (uIoc_subset_uIcc hy))

/-- Horizontal integrals agree across a holomorphic strip with vanishing connecting edges. -/
theorem integral_horizontal_eq_of_tendsto_edges {f : ℂ → ℂ} {c : ℝ}
    (hd : ∀ z : ℂ, z.im ∈ uIcc 0 c → DifferentiableAt ℂ f z)
    (h₀ : Integrable (fun x : ℝ => f (x : ℂ)))
    (hc : Integrable (fun x : ℝ => f ((x : ℂ) + (c : ℂ) * I)))
    (hr : Tendsto (fun T : ℝ => ∫ y in (0 : ℝ)..c,
      f ((T : ℂ) + (y : ℂ) * I)) atTop (𝓝 0))
    (hl : Tendsto (fun T : ℝ => ∫ y in (0 : ℝ)..c,
      f ((-T : ℝ) + (y : ℂ) * I)) atTop (𝓝 0)) :
    (∫ x : ℝ, f (x : ℂ)) = ∫ x : ℝ, f ((x : ℂ) + (c : ℂ) * I) := by
  have he (T : ℝ) :
      (∫ x in -T..T, f (x : ℂ)) - (∫ x in -T..T, f ((x : ℂ) + (c : ℂ) * I)) +
        I * (∫ y in (0 : ℝ)..c, f ((T : ℂ) + (y : ℂ) * I)) -
        I * (∫ y in (0 : ℝ)..c, f ((-T : ℝ) + (y : ℂ) * I)) = 0 := by
    have hh := integral_boundary_rect_eq_zero_of_differentiableOn f
      ((-T : ℝ) : ℂ) ((T : ℂ) + (c : ℂ) * I) (by
        intro z hz
        apply (hd z ?_).differentiableWithinAt
        simpa using hz.2)
    simpa using hh
  have ht := (((intervalIntegral_tendsto_integral h₀ tendsto_neg_atTop_atBot tendsto_id).sub
    (intervalIntegral_tendsto_integral hc tendsto_neg_atTop_atBot tendsto_id)).add
      (hr.const_mul I)).sub (hl.const_mul I)
  have hz := tendsto_nhds_unique ht (tendsto_const_nhds.congr (fun T => (he T).symm))
  simpa only [mul_zero, add_zero, sub_zero, sub_eq_zero] using hz

end Complex
