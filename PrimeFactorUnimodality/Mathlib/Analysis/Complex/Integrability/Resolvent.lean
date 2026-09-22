/-
Copyright (c) 2026 Jonas Whidden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonas Whidden
-/
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Integral.Prod

/-! # Resolvent pairing by an absolutely convergent Laplace integral

A pole strictly left of a vertical line has an exponentially decaying
half-line representation. Its product with any continuous integrable
height weight satisfies Fubini: the product norm separates into an
integrable exponential and the norm of that weight.

The separated-denominator bound in `integrable_div_vertical` also occurs
inside `Robin1984.integrable_paired_xi_atom`, Apache-2.0 revision
`bfa72aec0c25c8ee29cefe4449d778ff30412bee`,
`Robin1984.NicolasLandau.WeightedZeroInterchange`. Here the pole's real part
is arbitrary strictly to the left, and only Mathlib is imported.
-/

namespace Complex

noncomputable section

open MeasureTheory Set

/-- A pole separated from the contour preserves integrability of the weight. -/
theorem integrable_div_vertical {H : ℝ → ℂ} (hH : Integrable H)
    {c : ℝ} {ρ : ℂ} (hρ : ρ.re < c) :
    Integrable (fun t : ℝ => H t / ((c : ℂ) + (t : ℂ) * I - ρ)) := by
  have hpos : 0 < c - ρ.re := sub_pos.mpr hρ
  have hm : AEStronglyMeasurable (fun t : ℝ => H t / ((c : ℂ) + (t : ℂ) * I - ρ)) volume := by
    simp only [div_eq_mul_inv]
    exact hH.aestronglyMeasurable.fun_mul (by fun_prop)
  apply (hH.norm.div_const (c - ρ.re)).mono' hm
  filter_upwards with t
  have hden : c - ρ.re ≤ ‖(c : ℂ) + (t : ℂ) * I - ρ‖ := by
    simpa using re_le_norm ((c : ℂ) + (t : ℂ) * I - ρ)
  rw [norm_div]
  exact div_le_div_of_nonneg_left (norm_nonneg _) hpos hden

/-- Absolute product integrability for the half-line representation of a resolvent. -/
theorem integrable_exp_mul_vertical_prod {H : ℝ → ℂ}
    (hH : Integrable H) (hcont : Continuous H) {c : ℝ} {ρ : ℂ} (hρ : ρ.re < c) :
    Integrable (fun p : ℝ × ℝ => H p.2 *
      exp (-((c : ℂ) + (p.2 : ℂ) * I - ρ) * (p.1 : ℂ)))
      ((volume.restrict (Ioi (0 : ℝ))).prod volume) := by
  have hexp := integrableOn_exp_mul_Ioi (a := -(c - ρ.re)) (by linarith) 0
  apply (hexp.mul_prod hH.norm).mono' (by fun_prop)
  filter_upwards with p
  rw [norm_mul, norm_exp]
  have hre : (-((c : ℂ) + (p.2 : ℂ) * I - ρ) * (p.1 : ℂ)).re =
      -(c - ρ.re) * p.1 := by simp
  rw [hre, mul_comm]

/-- Pairing with a resolvent equals pairing the negative-frequency transform with an exponential. -/
theorem integral_div_vertical_eq_integral_exp {H : ℝ → ℂ}
    (hH : Integrable H) (hcont : Continuous H) {c : ℝ} {ρ : ℂ} (hρ : ρ.re < c) :
    (∫ t : ℝ, H t / ((c : ℂ) + (t : ℂ) * I - ρ)) =
      ∫ u : ℝ in Ioi 0, exp (-((c : ℂ) - ρ) * (u : ℂ)) *
        (∫ t : ℝ, exp (-((t : ℂ) * I) * (u : ℂ)) * H t) := by
  have hrep (t : ℝ) : H t / ((c : ℂ) + (t : ℂ) * I - ρ) =
      ∫ u : ℝ in Ioi 0, H t * exp (-((c : ℂ) + (t : ℂ) * I - ρ) * (u : ℂ)) := by
    rw [integral_const_mul, integral_exp_mul_complex_Ioi (by simpa using sub_neg.mpr hρ) 0]
    simp only [ofReal_zero, mul_zero, exp_zero, neg_div_neg_eq, mul_one_div]
  simp_rw [hrep]
  rw [← integral_integral_swap (integrable_exp_mul_vertical_prod hH hcont hρ)]
  apply integral_congr_ae
  filter_upwards with u
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards with t
  rw [← mul_assoc, ← exp_add]
  have he : -((c : ℂ) + (t : ℂ) * I - ρ) * (u : ℂ) =
      -((c : ℂ) - ρ) * (u : ℂ) + -((t : ℂ) * I) * (u : ℂ) := by ring
  rw [he, mul_comm]

end

end Complex
