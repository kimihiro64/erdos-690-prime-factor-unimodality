/-
Copyright (c) 2026 Jonas Whidden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonas Whidden
-/
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.Tactic.LinearCombination

/-! # Finite Laplace transforms and their endpoint terms

Two integrations by parts isolate the value at zero and a second-derivative
remainder. Only interval regularity is required; a weight need not extend
continuously by zero across the origin or vanish in a neighborhood of its
right endpoint.

The argument follows Kadiri's Laplace identity in section 3.1 of
*Une région explicite sans zéros pour la fonction zeta de Riemann*.
The interval integration-by-parts pattern also appears in
`Kadiri.laplaceTransform_ibp` in the Apache-2.0 repository
`kimihiro64/PrimeNumberTheoremAnd`, revision
`f6147e7572ab3abe5428101bc0b13627bcb005df`. This generalization uses only
Mathlib and does not import that project's explicit-formula assumptions.
-/

namespace Complex

noncomputable section

open MeasureTheory Set

/-- The Laplace integral of a complex weight over a finite interval beginning at zero. -/
def finiteLaplace (f : ℝ → ℂ) (d : ℝ) (s : ℂ) : ℂ :=
  ∫ t in (0 : ℝ)..d, exp (-s * (t : ℂ)) * f t

/-- Differentiating the exponential kernel with respect to its real integration variable. -/
theorem hasDerivAt_finiteLaplace_kernel (s : ℂ) (t : ℝ) :
    HasDerivAt (fun u : ℝ => exp (-s * (u : ℂ))) (-s * exp (-s * (t : ℂ))) t := by
  simpa [mul_assoc, mul_comm, mul_left_comm] using
    ((hasDerivAt_id t).ofReal_comp.const_mul (-s)).cexp

/-- A continuous weight gives an integrable finite Laplace kernel at every complex point. -/
theorem intervalIntegrable_finiteLaplace {f : ℝ → ℂ} {d : ℝ}
    (hf : ContinuousOn f (uIcc 0 d)) (s : ℂ) :
    IntervalIntegrable (fun t : ℝ => exp (-s * (t : ℂ)) * f t) volume 0 d := by
  have hk : Continuous (fun t : ℝ => exp (-s * (t : ℂ))) := by fun_prop
  exact (hk.continuousOn.mul hf).intervalIntegrable

/-- One integration by parts, retaining both endpoint values and avoiding division by `s`. -/
theorem mul_finiteLaplace_eq {f g : ℝ → ℂ} {d : ℝ} (hd : 0 ≤ d)
    (hf : ContinuousOn f (Icc 0 d)) (hg : ContinuousOn g (Icc 0 d))
    (hfg : ∀ t ∈ Ioo 0 d, HasDerivAt f (g t) t) (s : ℂ) :
    s * finiteLaplace f d s =
      f 0 - exp (-s * (d : ℂ)) * f d + finiteLaplace g d s := by
  have hf' : ContinuousOn f (uIcc 0 d) := by simpa only [uIcc_of_le hd] using hf
  have hg' : ContinuousOn g (uIcc 0 d) := by simpa only [uIcc_of_le hd] using hg
  have hk : Continuous (fun t : ℝ => exp (-s * (t : ℂ))) := by fun_prop
  have hdk : Continuous (fun t : ℝ => -s * exp (-s * (t : ℂ))) := by fun_prop
  have h := intervalIntegral.integral_mul_deriv_eq_deriv_mul_of_hasDerivAt
    (a := 0) (b := d) (u := f) (v := fun t : ℝ => exp (-s * (t : ℂ)))
    (u' := g) (v' := fun t : ℝ => -s * exp (-s * (t : ℂ))) hf' hk.continuousOn
    (fun t ht => hfg t (by simpa only [min_eq_left hd, max_eq_right hd] using ht))
    (fun t _ => hasDerivAt_finiteLaplace_kernel s t)
    hg'.intervalIntegrable (hdk.intervalIntegrable 0 d)
  have hleft : (∫ t in (0 : ℝ)..d, f t * (-s * exp (-s * (t : ℂ)))) =
      -s * finiteLaplace f d s := by
    rw [finiteLaplace, ← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro t ht
    ring
  have hright : (∫ t in (0 : ℝ)..d, g t * exp (-s * (t : ℂ))) =
      finiteLaplace g d s := by simp only [finiteLaplace, mul_comm]
  rw [hleft, hright] at h
  simp only [ofReal_zero, mul_zero, exp_zero, mul_one] at h
  linear_combination -h

/-- Two integrations by parts with all endpoint terms explicit. -/
theorem sq_mul_finiteLaplace_eq {f g h : ℝ → ℂ} {d : ℝ} (hd : 0 ≤ d)
    (hf : ContinuousOn f (Icc 0 d)) (hg : ContinuousOn g (Icc 0 d))
    (hh : ContinuousOn h (Icc 0 d))
    (hfg : ∀ t ∈ Ioo 0 d, HasDerivAt f (g t) t)
    (hgh : ∀ t ∈ Ioo 0 d, HasDerivAt g (h t) t) (s : ℂ) :
    s ^ 2 * finiteLaplace f d s =
      s * f 0 + g 0 - exp (-s * (d : ℂ)) * (s * f d + g d) + finiteLaplace h d s := by
  have h₁ := mul_finiteLaplace_eq hd hf hg hfg s
  have h₂ := mul_finiteLaplace_eq hd hg hh hgh s
  linear_combination s * h₁ + h₂

/-- Vanishing endpoint derivatives isolate the pole and the second-derivative remainder. -/
theorem finiteLaplace_eq_pole_add {f g h : ℝ → ℂ} {d : ℝ} (hd : 0 ≤ d)
    (hf : ContinuousOn f (Icc 0 d)) (hg : ContinuousOn g (Icc 0 d))
    (hh : ContinuousOn h (Icc 0 d))
    (hfg : ∀ t ∈ Ioo 0 d, HasDerivAt f (g t) t)
    (hgh : ∀ t ∈ Ioo 0 d, HasDerivAt g (h t) t)
    (hfd : f d = 0) (hg₀ : g 0 = 0) (hgd : g d = 0) {s : ℂ} (hs : s ≠ 0) :
    finiteLaplace f d s = f 0 / s + finiteLaplace h d s / s ^ 2 := by
  have hid := sq_mul_finiteLaplace_eq hd hf hg hh hfg hgh s
  simp only [hfd, hg₀, hgd, mul_zero, add_zero, sub_zero] at hid
  field_simp
  linear_combination hid

end

end Complex
