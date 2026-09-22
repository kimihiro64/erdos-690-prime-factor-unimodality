/-
Copyright (c) 2026 Jonas Whidden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonas Whidden
-/
import PrimeFactorUnimodality.Mathlib.Analysis.Complex.FiniteLaplace.ContourBounds
import PrimeFactorUnimodality.Mathlib.Analysis.Complex.Integrability.Resolvent

/-! # Exact pairing of a smoothed contour weight with a resolvent

Absolute Fubini and Fourier inversion evaluate a pole strictly left of the
contour. The result is the pole-subtracted finite Laplace transform at the
shifted pole, with its full angular-frequency normalization. The constant
regularizer has zero integral. No contour displacement is assumed.
-/

namespace Complex

noncomputable section

open MeasureTheory Set

variable {f g h : ℝ → ℂ} {d M : ℝ}
  (hd : 0 ≤ d) (hM : 0 ≤ M)
  (hf : ContinuousOn f (Icc 0 d)) (hg : ContinuousOn g (Icc 0 d))
  (hh : ContinuousOn h (Icc 0 d))
  (hfg : ∀ u ∈ Ioo 0 d, HasDerivAt f (g u) u)
  (hgh : ∀ u ∈ Ioo 0 d, HasDerivAt g (h u) u)
  (hfd : f d = 0) (hg₀ : g 0 = 0) (hgd : g d = 0)
  (hbound : ∀ u ∈ Icc 0 d, ‖h u‖ ≤ M)
  {s : ℂ} {c : ℝ} (hcs : c < s.re)

include hd hM hf hg hh hfg hgh hfd hg₀ hgd hbound hcs

/-- Absolute inversion with the negative-height convention used by the shifted contour. -/
theorem integral_exp_mul_finiteLaplace_sub_pole_contour (x : ℝ) :
    (1 / (2 * (Real.pi : ℂ))) * (∫ t : ℝ, exp (-((t : ℂ) * I) * (x : ℂ)) *
      (finiteLaplace f d (s - ((c : ℂ) + (t : ℂ) * I)) -
        f 0 / (s - ((c : ℂ) + (t : ℂ) * I)))) =
      exp (-(s - c) * (x : ℂ)) * finiteLaplaceRemainderSource f d x := by
  have hi := integral_finiteLaplace_sub_pole_vertical hd hM hf hg hh hfg hgh
    hfd hg₀ hgd hbound (s := s - c) (by simpa using sub_pos.mpr hcs) x
  have hneg := (Measure.measurePreserving_neg (volume : Measure ℝ)).integral_comp
    (Homeomorph.neg ℝ).measurableEmbedding
    (fun t : ℝ => exp ((t : ℂ) * I * (x : ℂ)) *
      (finiteLaplace f d ((s - c) + (t : ℂ) * I) -
        f 0 / ((s - c) + (t : ℂ) * I)))
  have heq := (congrArg (fun z : ℂ => (1 / (2 * (Real.pi : ℂ))) * z) hneg).trans hi
  simpa only [ofReal_neg, neg_mul, sub_eq_add_neg, neg_add, add_assoc] using heq

/-- Exact pole pairing for every pole strictly left of the contour. -/
theorem integral_finiteLaplace_sub_pole_div_vertical {ρ : ℂ} (hρ : ρ.re < c) :
    (1 / (2 * (Real.pi : ℂ))) * (∫ t : ℝ,
      (finiteLaplace f d (s - ((c : ℂ) + (t : ℂ) * I)) -
        f 0 / (s - ((c : ℂ) + (t : ℂ) * I))) /
      ((c : ℂ) + (t : ℂ) * I - ρ)) = finiteLaplace f d (s - ρ) - f 0 / (s - ρ) := by
  let H : ℝ → ℂ := fun t => finiteLaplace f d (s - ((c : ℂ) + (t : ℂ) * I)) -
    f 0 / (s - ((c : ℂ) + (t : ℂ) * I))
  have hH : Integrable H := integrable_finiteLaplace_sub_pole_contour hd hM hf hg hh hfg hgh
    hfd hg₀ hgd hbound hcs
  have hcont : Continuous H := by
    have hne (t : ℝ) : s - ((c : ℂ) + (t : ℂ) * I) ≠ 0 := by
      intro heq
      have hre := congrArg Complex.re heq
      simp only [sub_re, add_re, mul_re, ofReal_re, I_re, I_im, ofReal_im,
        mul_zero, zero_mul, sub_zero, add_zero, zero_re] at hre
      linarith
    have hF : Continuous (fun t : ℝ => finiteLaplace f d (s - ((c : ℂ) + (t : ℂ) * I))) := by
      simpa only [sub_add_eq_sub_sub] using continuous_finiteLaplace_vertical hd hf (s - c)
    exact hF.sub (continuous_const.div (by fun_prop) hne)
  change (1 / (2 * (Real.pi : ℂ))) * (∫ t : ℝ, H t / _) = _
  rw [integral_div_vertical_eq_integral_exp hH hcont hρ, ← integral_const_mul]
  calc
    _ = ∫ u : ℝ in Ioi 0, exp (-(s - ρ) * (u : ℂ)) *
        finiteLaplaceRemainderSource f d u := by
      apply integral_congr_ae
      filter_upwards with u
      rw [mul_left_comm (1 / (2 * (Real.pi : ℂ))),
        integral_exp_mul_finiteLaplace_sub_pole_contour hd hM hf hg hh hfg hgh
          hfd hg₀ hgd hbound hcs u, ← mul_assoc, ← exp_add]
      congr 2
      ring
    _ = ∫ u : ℝ, exp (-(s - ρ) * (u : ℂ)) * finiteLaplaceRemainderSource f d u := by
      apply setIntegral_eq_integral_of_forall_compl_eq_zero
      intro u hu
      rw [finiteLaplaceRemainderSource_of_nonpos f d (not_lt.mp hu), mul_zero]
    _ = _ := integral_exp_mul_finiteLaplaceRemainderSource hd hf hfd
      (by simp only [sub_re]; linarith)

/-- The additional constant in a genus-one atom contributes zero. -/
theorem integral_finiteLaplace_sub_pole_mul_hadamardAtom {ρ : ℂ} (hρ : ρ.re < c) :
    (1 / (2 * (Real.pi : ℂ))) * (∫ t : ℝ,
      (finiteLaplace f d (s - ((c : ℂ) + (t : ℂ) * I)) -
        f 0 / (s - ((c : ℂ) + (t : ℂ) * I))) *
      (1 / ((c : ℂ) + (t : ℂ) * I - ρ) + 1 / ρ)) =
      finiteLaplace f d (s - ρ) - f 0 / (s - ρ) := by
  have hH := integrable_finiteLaplace_sub_pole_contour hd hM hf hg hh hfg hgh
    hfd hg₀ hgd hbound hcs
  simp_rw [mul_add, mul_one_div]
  rw [integral_add (integrable_div_vertical hH hρ) (hH.div_const ρ), integral_div,
    integral_finiteLaplace_sub_pole_contour_eq_zero hd hM hf hg hh hfg hgh
      hfd hg₀ hgd hbound hcs, zero_div, add_zero]
  exact integral_finiteLaplace_sub_pole_div_vertical hd hM hf hg hh hfg hgh
    hfd hg₀ hgd hbound hcs hρ

end

end Complex
