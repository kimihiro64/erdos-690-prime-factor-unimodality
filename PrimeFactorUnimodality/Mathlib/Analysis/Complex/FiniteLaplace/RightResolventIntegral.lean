/-
Copyright (c) 2026 Jonas Whidden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonas Whidden
-/
import PrimeFactorUnimodality.Mathlib.Analysis.Complex.FiniteLaplace.ResolventIntegral
import PrimeFactorUnimodality.Mathlib.Analysis.Complex.Integrability.RightResolvent

/-! # Vanishing of smoothed contour pairings with right-hand poles

The inverse Laplace source vanishes at nonpositive arguments. Absolute
Fubini then shows that a pole strictly right of the contour contributes
zero. Reflection of a left-hand regularized atom gives such a pole.
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

/-- At a nonpositive time the full, unnormalized inverse contour integral vanishes. -/
theorem integral_exp_mul_finiteLaplace_sub_pole_contour_eq_zero {x : ℝ} (hx : x ≤ 0) :
    (∫ t : ℝ, exp (-((t : ℂ) * I) * (x : ℂ)) *
      (finiteLaplace f d (s - ((c : ℂ) + (t : ℂ) * I)) -
        f 0 / (s - ((c : ℂ) + (t : ℂ) * I)))) = 0 := by
  have hi := integral_exp_mul_finiteLaplace_sub_pole_contour hd hM hf hg hh hfg hgh
    hfd hg₀ hgd hbound hcs x
  rw [finiteLaplaceRemainderSource_of_nonpos f d hx, mul_zero] at hi
  exact (mul_eq_zero.mp hi).resolve_left
    (one_div_ne_zero (mul_ne_zero (by norm_num) (ofReal_ne_zero.mpr Real.pi_ne_zero)))

/-- A right-hand pole pairs to zero with the actual pole-subtracted Laplace weight. -/
theorem integral_finiteLaplace_sub_pole_div_vertical_of_right {ρ : ℂ} (hρ : c < ρ.re) :
    (∫ t : ℝ, (finiteLaplace f d (s - ((c : ℂ) + (t : ℂ) * I)) -
        f 0 / (s - ((c : ℂ) + (t : ℂ) * I))) /
      ((c : ℂ) + (t : ℂ) * I - ρ)) = 0 := by
  let H : ℝ → ℂ := fun t => finiteLaplace f d (s - ((c : ℂ) + (t : ℂ) * I)) -
    f 0 / (s - ((c : ℂ) + (t : ℂ) * I))
  have hrep := integral_div_rev_vertical_eq_integral_exp
    (integrable_finiteLaplace_sub_pole_contour hd hM hf hg hh hfg hgh hfd hg₀ hgd hbound hcs)
    (continuous_finiteLaplace_sub_pole_contour hd hf hcs) hρ
  have hzero : (∫ t : ℝ, H t / (ρ - ((c : ℂ) + (t : ℂ) * I))) = 0 := by
    rw [hrep]
    apply integral_eq_zero_of_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    have hi := integral_exp_mul_finiteLaplace_sub_pole_contour_eq_zero hd hM hf hg hh hfg hgh
      hfd hg₀ hgd hbound hcs (x := -u) (by exact neg_nonpos.mpr hu.le)
    have hi' : (∫ t : ℝ, exp ((t : ℂ) * I * (u : ℂ)) * H t) = 0 := by
      simpa only [ofReal_neg, mul_neg, neg_mul, neg_neg] using hi
    rw [hi', mul_zero]
    rfl
  have heq (t : ℝ) : H t / ((c : ℂ) + (t : ℂ) * I - ρ) =
      -(H t / (ρ - ((c : ℂ) + (t : ℂ) * I))) := by rw [← neg_sub, div_neg]
  change (∫ t : ℝ, H t / _) = _
  simp_rw [heq]
  rw [integral_neg, hzero, neg_zero]

/-- Reflection across the contour turns a left-hand atom into a vanishing right-hand pole. -/
theorem integral_finiteLaplace_sub_pole_mul_reflected_atom_eq_zero {ρ : ℂ} (hρ : ρ.re < c) :
    (∫ t : ℝ, (finiteLaplace f d (s - ((c : ℂ) + (t : ℂ) * I)) -
        f 0 / (s - ((c : ℂ) + (t : ℂ) * I))) *
      (1 / ((c : ℂ) - (t : ℂ) * I - ρ) + 1 / ρ)) = 0 := by
  let pole : ℂ := 2 * c - ρ
  have hpole : c < pole.re := by
    have heq : pole.re = 2 * c - ρ.re := by simp [pole]
    rw [heq]
    linarith
  have hH := integrable_finiteLaplace_sub_pole_contour hd hM hf hg hh hfg hgh
    hfd hg₀ hgd hbound hcs
  have heq (t : ℝ) : (c : ℂ) - (t : ℂ) * I - ρ = -((c : ℂ) + (t : ℂ) * I - pole) := by
    dsimp [pole]
    ring
  simp_rw [mul_add, mul_one_div, heq, div_neg]
  have hn : Integrable (fun t : ℝ => -((finiteLaplace f d
      (s - ((c : ℂ) + (t : ℂ) * I)) - f 0 / (s - ((c : ℂ) + (t : ℂ) * I))) /
      ((c : ℂ) + (t : ℂ) * I - pole))) := (integrable_div_vertical_of_right hH hpole).neg
  rw [integral_add hn (hH.div_const ρ), integral_neg,
    integral_finiteLaplace_sub_pole_div_vertical_of_right hd hM hf hg hh hfg hgh
      hfd hg₀ hgd hbound hcs hpole, integral_div,
    integral_finiteLaplace_sub_pole_contour_eq_zero hd hM hf hg hh hfg hgh
      hfd hg₀ hgd hbound hcs, neg_zero, zero_div, add_zero]

end

end Complex
