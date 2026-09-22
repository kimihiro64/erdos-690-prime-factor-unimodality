/-
Copyright (c) 2026 Jonas Whidden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonas Whidden
-/
import PrimeFactorUnimodality.Mathlib.Analysis.Complex.FiniteLaplace.Monotonicity

/-! # Weighted integral bounds for finite Laplace transforms

Retain the exact transform of the source norm instead of replacing it by
a supremum. This is useful on negative vertical lines, where the actual
weighted integral is needed for sharp constants in remainder estimates.
-/

namespace Complex

noncomputable section

open MeasureTheory Set

/-- The source-norm transform on the real axis bounds the complex transform. -/
theorem norm_finiteLaplace_le_weighted_norm {f : ℝ → ℂ} {d : ℝ}
    (hd : 0 ≤ d) (hf : ContinuousOn f (Icc 0 d)) (s : ℂ) :
    ‖finiteLaplace f d s‖ ≤
      (finiteLaplace (fun u => (‖f u‖ : ℂ)) d (s.re : ℂ)).re := by
  have hn : ContinuousOn (fun u => ‖f u‖) (uIcc 0 d) := by
    simpa only [uIcc_of_le hd] using hf.norm
  rw [re_finiteLaplace_ofReal hn]
  refine (intervalIntegral.norm_integral_le_integral_norm hd).trans_eq ?_
  apply intervalIntegral.integral_congr
  intro u _
  simp [norm_exp]

/-- Two integrations by parts retain the exact weighted norm of the second derivative. -/
theorem norm_finiteLaplace_sub_pole_le_weighted_norm {f g h : ℝ → ℂ} {d : ℝ}
    (hd : 0 ≤ d) (hf : ContinuousOn f (Icc 0 d)) (hg : ContinuousOn g (Icc 0 d))
    (hh : ContinuousOn h (Icc 0 d))
    (hfg : ∀ u ∈ Ioo 0 d, HasDerivAt f (g u) u)
    (hgh : ∀ u ∈ Ioo 0 d, HasDerivAt g (h u) u)
    (hfd : f d = 0) (hg₀ : g 0 = 0) (hgd : g d = 0) {s : ℂ} (hs : s ≠ 0) :
    ‖finiteLaplace f d s - f 0 / s‖ ≤
      (finiteLaplace (fun u => (‖h u‖ : ℂ)) d (s.re : ℂ)).re / ‖s‖ ^ 2 := by
  rw [finiteLaplace_eq_pole_add hd hf hg hh hfg hgh hfd hg₀ hgd hs,
    add_sub_cancel_left, norm_div, norm_pow]
  exact div_le_div_of_nonneg_right (norm_finiteLaplace_le_weighted_norm hd hh s) (sq_nonneg _)

end

end Complex
