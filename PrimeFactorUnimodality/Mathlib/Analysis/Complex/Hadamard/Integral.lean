/-
Copyright (c) 2026 Jonas Whidden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonas Whidden
-/
import PrimeFactorUnimodality.Mathlib.Analysis.Complex.Hadamard.IntegralBounds
import PrimeFactorUnimodality.Mathlib.MeasureTheory.Integral.Bochner.Series

/-! # Absolute interchange of weighted Hadamard series and vertical integrals

A finite three-halves moment and an upper real-part bound suffice for
absolute interchange of the complete regularized series. Indices may
repeat zeros to retain multiplicity. Adapted from
`Robin1984.summable_integral_norm_paired_xi_atoms` and
`Robin1984.integral_tsum_paired_xi_atoms`, Apache-2.0 revision
`bfa72aec0c25c8ee29cefe4449d778ff30412bee`, `WeightedZeroInterchange.lean`.
The generalization removes its RH hypothesis: zeros need not share a real
part, and the contour can be any positive line strictly to their right.
-/

namespace Complex

noncomputable section

open MeasureTheory

/-- The integrated norms of the entire regularized zero family are summable. -/
theorem summable_integral_norm_mul_hadamardAtoms {ι : Type*} {ρ : ι → ℂ}
    {c B C : ℝ} (hc : 0 < c) (hBc : B < c) (hC : 0 ≤ C)
    (hρ₀ : ∀ i, ρ i ≠ 0) (hρ : ∀ i, (ρ i).re ≤ B)
    (hMoment : Summable (fun i => ‖ρ i‖⁻¹ ^ (3 / 2 : ℝ)))
    {H : ℝ → ℂ} (hH : Integrable H)
    (hBound : ∀ t, ‖H t‖ ≤ C / ‖(c : ℂ) + (t : ℂ) * I‖ ^ 2) :
    Summable (fun i => ∫ t : ℝ,
      ‖H t * (1 / ((c : ℂ) + (t : ℂ) * I - ρ i) + 1 / ρ i)‖) := by
  let K : ℝ → ℝ → ℝ := fun a t => ‖(a : ℂ) + (t : ℂ) * I‖⁻¹ ^ (3 / 2 : ℝ)
  have hKc : Integrable (K c) := integrable_inv_rpow_norm_vertical hc (by norm_num)
  have hKg : Integrable (K (c - B)) :=
    integrable_inv_rpow_norm_vertical (sub_pos.mpr hBc) (by norm_num)
  have hmajor (i : ι) : (∫ t : ℝ,
      ‖H t * (1 / ((c : ℂ) + (t : ℂ) * I - ρ i) + 1 / ρ i)‖) ≤
      (2 * C * ((∫ t : ℝ, K c t) + ∫ t : ℝ, K (c - B) t)) *
        ‖ρ i‖⁻¹ ^ (3 / 2 : ℝ) := by
    have hshift := hKg.comp_sub_right (ρ i).im
    have hmaj := (hKc.add hshift).const_mul (2 * C * ‖ρ i‖⁻¹ ^ (3 / 2 : ℝ))
    have hF := integrable_mul_hadamardAtom_vertical hH ((hρ i).trans_lt hBc)
    calc
      _ ≤ ∫ t : ℝ, (2 * C * ‖ρ i‖⁻¹ ^ (3 / 2 : ℝ)) *
          (K c t + K (c - B) (t - (ρ i).im)) := by
        apply integral_mono_ae hF.norm hmaj
        filter_upwards with t
        exact norm_mul_hadamardAtom_vertical_le hc hBc hC (hρ₀ i) (hρ i) t (hBound t)
      _ = _ := by
        rw [integral_const_mul, integral_add hKc hshift, integral_sub_right_eq_self]
        ring
  exact Summable.of_nonneg_of_le
    (fun i => integral_nonneg (fun t => norm_nonneg _)) hmajor
    (hMoment.mul_left _)

/-- The complete weighted regularized series is an integrable function. -/
theorem integrable_mul_tsum_hadamardAtoms {ι : Type*} [Countable ι] {ρ : ι → ℂ}
    {c B C : ℝ} (hc : 0 < c) (hBc : B < c) (hC : 0 ≤ C)
    (hρ₀ : ∀ i, ρ i ≠ 0) (hρ : ∀ i, (ρ i).re ≤ B)
    (hMoment : Summable (fun i => ‖ρ i‖⁻¹ ^ (3 / 2 : ℝ)))
    {H : ℝ → ℂ} (hH : Integrable H)
    (hBound : ∀ t, ‖H t‖ ≤ C / ‖(c : ℂ) + (t : ℂ) * I‖ ^ 2) :
    Integrable (fun t : ℝ => H t *
      (∑' i, (1 / ((c : ℂ) + (t : ℂ) * I - ρ i) + 1 / ρ i))) := by
  have h := integrable_tsum_of_summable_integral_norm
    (fun i => integrable_mul_hadamardAtom_vertical hH ((hρ i).trans_lt hBc))
    (summable_integral_norm_mul_hadamardAtoms hc hBc hC hρ₀ hρ hMoment hH hBound)
  simpa only [tsum_mul_left] using h

/-- Fubini for the full multiplicity-indexed regularized family. -/
theorem tsum_integral_mul_hadamardAtoms {ι : Type*} [Countable ι] {ρ : ι → ℂ}
    {c B C : ℝ} (hc : 0 < c) (hBc : B < c) (hC : 0 ≤ C)
    (hρ₀ : ∀ i, ρ i ≠ 0) (hρ : ∀ i, (ρ i).re ≤ B)
    (hMoment : Summable (fun i => ‖ρ i‖⁻¹ ^ (3 / 2 : ℝ)))
    {H : ℝ → ℂ} (hH : Integrable H)
    (hBound : ∀ t, ‖H t‖ ≤ C / ‖(c : ℂ) + (t : ℂ) * I‖ ^ 2) :
    (∑' i, ∫ t : ℝ, H t * (1 / ((c : ℂ) + (t : ℂ) * I - ρ i) + 1 / ρ i)) =
      ∫ t : ℝ, H t * (∑' i, (1 / ((c : ℂ) + (t : ℂ) * I - ρ i) + 1 / ρ i)) := by
  rw [integral_tsum_of_summable_integral_norm
    (fun i => integrable_mul_hadamardAtom_vertical hH ((hρ i).trans_lt hBc))
    (summable_integral_norm_mul_hadamardAtoms hc hBc hC hρ₀ hρ hMoment hH hBound)]
  apply integral_congr_ae
  filter_upwards with t
  exact tsum_mul_left

end

end Complex
