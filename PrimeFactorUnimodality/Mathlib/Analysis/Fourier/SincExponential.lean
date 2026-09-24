/-
Copyright (c) 2026 Jonas Whidden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonas Whidden
-/
import PrimeFactorUnimodality.Mathlib.Analysis.Fourier.ExponentialAliasing
import PrimeFactorUnimodality.Mathlib.Analysis.Fourier.ExponentialIntegral
import PrimeFactorUnimodality.Mathlib.Analysis.Fourier.SincError

/-! # Explicit sampling error from a finite exponential Fourier envelope

The off-cell integral is evaluated exactly. A uniform geometric bound on
aliases is integrated over the central cell. This bound is conservative
compared with integrating each alias separately, but retains exponential
decay in the frequency cutoff and does not require bounded variation.
-/

open MeasureTheory Filter Asymptotics
open scoped FourierTransform

namespace Fourier

/-- A genuine exponentially decaying transform gives a completely explicit sinc error. -/
theorem norm_sub_sincSeries_le_of_finite_exp_bound {ι : Type*}
    {s : Finset ι} {c a : ι → ℝ} {f : ℝ → ℂ}
    (hc : Continuous f) (hi : Integrable f) {b : ℝ} (hb : 1 < b)
    (hd : f =O[cocompact ℝ] (fun t => |t| ^ (-b)))
    (hc₀ : ∀ i ∈ s, 0 ≤ c i) (ha : ∀ i ∈ s, 0 < a i)
    (hF : ∀ x, ‖𝓕 f x‖ ≤ ∑ i ∈ s, c i * Real.exp (-a i * |x|)) (t : ℝ) :
    ‖f t - ∑' n : ℤ, f n * (Real.sinc (Real.pi * (t - n)) : ℂ)‖ ≤
      2 * (∑ i ∈ s, c i * (Real.exp (-a i / 2) / a i)) +
      2 * (∑ i ∈ s, c i * (Real.exp (-a i / 2) / (1 - Real.exp (-a i)))) := by
  have hm : AEStronglyMeasurable (𝓕 f) :=
    (VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar
      (innerSL ℝ).continuous₂ hi).aestronglyMeasurable
  have hs (x : ℝ) : Summable (fun n : ℤ => 𝓕 f (x + n)) := by
    simpa only [mul_one] using summable_lattice_of_finite_exp_bound_margin
      hc₀ ha (by norm_num : (0 : ℝ) < 1) (u := x) (d := 1 - |x|) (by linarith) hF
  have hAlias (x : ℝ) (hx : x ∈ Set.Icc (-1 / 2 : ℝ) (1 / 2 : ℝ)) :
      ‖(∑' n : ℤ, 𝓕 f (x + n)) - 𝓕 f x‖ ≤
        2 * ∑ i ∈ s, c i * (Real.exp (-a i / 2) / (1 - Real.exp (-a i))) := by
    have hx' : |x| ≤ (1 : ℝ) / 2 := abs_le.mpr ⟨by linarith [hx.1], hx.2⟩
    simpa only [mul_one] using norm_periodization_sub_le_of_finite_exp_bound
      hc₀ ha (by norm_num : (0 : ℝ) < 1) hx' hF
  have ht := integral_norm_compl_le_of_finite_exp_bound ha hm
    (by norm_num : (0 : ℝ) ≤ 1 / 2) hF
  have he := norm_sub_sincSeries_le hc hi (integrable_of_finite_exp_bound ha hm hF)
    hb hd hs hAlias t
  apply he.trans
  exact add_le_add (by simpa only [mul_one_div, neg_div] using ht) le_rfl

end Fourier
