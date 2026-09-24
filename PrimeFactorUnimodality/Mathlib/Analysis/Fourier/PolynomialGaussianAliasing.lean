/-
Copyright (c) 2026 Jonas Whidden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonas Whidden
-/
import PrimeFactorUnimodality.Mathlib.Analysis.Fourier.ExponentialAliasing
import PrimeFactorUnimodality.Mathlib.Analysis.SpecialFunctions.Gaussian.TailBound

/-! # Closed aliasing bounds for polynomial Gaussian envelopes

The tangent at half a period has positive decay rate precisely past the
Gaussian polynomial's peak. Exact geometric summation cancels the tangent
normalization, leaving a closed bound with no unevaluated tail integrals.
-/

namespace Fourier

noncomputable section

private def gaussianAliasRate (k : ℕ) (b B : ℝ) : ℝ := b * B - 2 * (k : ℝ) / B

private def gaussianAliasCoeff (k : ℕ) (C b B : ℝ) : ℝ :=
  C * (B / 2) ^ k * Real.exp (-b * (B / 2) ^ 2) *
    Real.exp (gaussianAliasRate k b B * (B / 2))

private theorem gaussianAliasRate_pos (k : ℕ) {b B : ℝ} (hB : 0 < B)
    (hk : 2 * (k : ℝ) < b * B ^ 2) : 0 < gaussianAliasRate k b B := by
  apply sub_pos.mpr
  apply (div_lt_iff₀ hB).mpr
  nlinarith

private theorem gaussianAliasCoeff_nonneg (k : ℕ) {C b B : ℝ} (hC : 0 ≤ C) (hB : 0 < B) :
    0 ≤ gaussianAliasCoeff k C b B := by
  unfold gaussianAliasCoeff
  positivity

private theorem polynomialGaussian_le_exp (k : ℕ) {C b B : ℝ}
    (hC : 0 ≤ C) (hb : 0 ≤ b) (hB : 0 < B) (x : ℝ) :
    C * |x| ^ k * Real.exp (-b * x ^ 2) ≤
      gaussianAliasCoeff k C b B * Real.exp (-gaussianAliasRate k b B * |x|) := by
  have he : 2 * b * (B / 2) - (k : ℝ) / (B / 2) = gaussianAliasRate k b B := by
    unfold gaussianAliasRate
    field_simp
  have ht := mul_le_mul_of_nonneg_left
    (Real.abs_pow_mul_exp_neg_mul_sq_le_exp k hb (half_pos hB) x) hC
  rw [he] at ht
  simpa only [gaussianAliasCoeff, mul_assoc] using ht

private theorem gaussianAliasCoeff_cancel (k : ℕ) (C b : ℝ) {B : ℝ} (hB : 0 < B) :
    2 * (gaussianAliasCoeff k C b B *
      (Real.exp (-gaussianAliasRate k b B * B / 2) /
        (1 - Real.exp (-gaussianAliasRate k b B * B)))) =
      2 * C * (B / 2) ^ k * Real.exp (-b * (B / 2) ^ 2) /
        (1 - Real.exp (2 * (k : ℝ) - b * B ^ 2)) := by
  have he : -gaussianAliasRate k b B * B = 2 * (k : ℝ) - b * B ^ 2 := by
    unfold gaussianAliasRate
    field_simp
    ring
  have hc : Real.exp (gaussianAliasRate k b B * (B / 2)) *
      Real.exp (-gaussianAliasRate k b B * B / 2) = 1 := by
    rw [← Real.exp_add, show gaussianAliasRate k b B * (B / 2) +
      -gaussianAliasRate k b B * B / 2 = 0 by ring, Real.exp_zero]
  unfold gaussianAliasCoeff
  calc
    _ = (2 * C * (B / 2) ^ k * Real.exp (-b * (B / 2) ^ 2) /
        (1 - Real.exp (-gaussianAliasRate k b B * B))) *
        (Real.exp (gaussianAliasRate k b B * (B / 2)) *
          Real.exp (-gaussianAliasRate k b B * B / 2)) := by ring
    _ = _ := by rw [hc, mul_one, he]

variable {E : Type*} [NormedAddCommGroup E] [CompleteSpace E]

/-- A polynomial Gaussian majorant proves convergence of the full central-cell periodization. -/
theorem summable_lattice_of_polynomialGaussian_bound (k : ℕ) {C b B u : ℝ} {f : ℝ → E}
    (hC : 0 ≤ C) (hb : 0 ≤ b) (hB : 0 < B) (hk : 2 * (k : ℝ) < b * B ^ 2)
    (hu : |u| ≤ B / 2) (hf : ∀ x, ‖f x‖ ≤ C * |x| ^ k * Real.exp (-b * x ^ 2)) :
    Summable (fun n : ℤ => f (u + (n : ℝ) * B)) := by
  apply summable_lattice_of_finite_exp_bound (s := {(0 : ℕ)})
    (c := fun _ => gaussianAliasCoeff k C b B) (a := fun _ => gaussianAliasRate k b B)
    (fun _ _ => gaussianAliasCoeff_nonneg k hC hB)
    (fun _ _ => gaussianAliasRate_pos k hB hk) hB hu
  intro x
  simpa only [Finset.sum_singleton] using (hf x).trans (polynomialGaussian_le_exp k hC hb hB x)

/-- The complete aliasing error is bounded by one explicit geometric expression. -/
theorem norm_periodization_sub_le_of_polynomialGaussian_bound (k : ℕ)
    {C b B u : ℝ} {f : ℝ → E} (hC : 0 ≤ C) (hb : 0 ≤ b) (hB : 0 < B)
    (hk : 2 * (k : ℝ) < b * B ^ 2) (hu : |u| ≤ B / 2)
    (hf : ∀ x, ‖f x‖ ≤ C * |x| ^ k * Real.exp (-b * x ^ 2)) :
    ‖(∑' n : ℤ, f (u + (n : ℝ) * B)) - f u‖ ≤
      2 * C * (B / 2) ^ k * Real.exp (-b * (B / 2) ^ 2) /
        (1 - Real.exp (2 * (k : ℝ) - b * B ^ 2)) := by
  have ht := norm_periodization_sub_le_of_finite_exp_bound (s := {(0 : ℕ)})
    (c := fun _ => gaussianAliasCoeff k C b B) (a := fun _ => gaussianAliasRate k b B)
    (fun _ _ => gaussianAliasCoeff_nonneg k hC hB)
    (fun _ _ => gaussianAliasRate_pos k hB hk) hB hu (fun x =>
      by simpa only [Finset.sum_singleton] using
        (hf x).trans (polynomialGaussian_le_exp k hC hb hB x))
  simpa only [Finset.sum_singleton, gaussianAliasCoeff_cancel k C b hB] using ht

section FiniteEnvelope

variable {ι : Type*} {s : Finset ι} {k : ι → ℕ} {C : ι → ℝ} {b B u : ℝ} {f : ℝ → E}

/-- A finite mixture of polynomial Gaussian majorants still gives lattice convergence. -/
theorem summable_lattice_of_finite_polynomialGaussian_bound
    (hC : ∀ i ∈ s, 0 ≤ C i) (hb : 0 ≤ b) (hB : 0 < B)
    (hk : ∀ i ∈ s, 2 * (k i : ℝ) < b * B ^ 2) (hu : |u| ≤ B / 2)
    (hf : ∀ x, ‖f x‖ ≤ ∑ i ∈ s, C i * |x| ^ k i * Real.exp (-b * x ^ 2)) :
    Summable (fun n : ℤ => f (u + (n : ℝ) * B)) := by
  apply summable_lattice_of_finite_exp_bound
    (c := fun i => gaussianAliasCoeff (k i) (C i) b B)
    (a := fun i => gaussianAliasRate (k i) b B)
    (fun i hi => gaussianAliasCoeff_nonneg (k i) (hC i hi) hB)
    (fun i hi => gaussianAliasRate_pos (k i) hB (hk i hi)) hB hu
  intro x
  exact (hf x).trans (Finset.sum_le_sum fun i hi =>
    polynomialGaussian_le_exp (k i) (hC i hi) hb hB x)

/-- Every polynomial degree retains its own explicit geometric alias budget. -/
theorem norm_periodization_sub_le_of_finite_polynomialGaussian_bound
    (hC : ∀ i ∈ s, 0 ≤ C i) (hb : 0 ≤ b) (hB : 0 < B)
    (hk : ∀ i ∈ s, 2 * (k i : ℝ) < b * B ^ 2) (hu : |u| ≤ B / 2)
    (hf : ∀ x, ‖f x‖ ≤ ∑ i ∈ s, C i * |x| ^ k i * Real.exp (-b * x ^ 2)) :
    ‖(∑' n : ℤ, f (u + (n : ℝ) * B)) - f u‖ ≤
      ∑ i ∈ s, 2 * C i * (B / 2) ^ k i * Real.exp (-b * (B / 2) ^ 2) /
        (1 - Real.exp (2 * (k i : ℝ) - b * B ^ 2)) := by
  have ht := norm_periodization_sub_le_of_finite_exp_bound
    (c := fun i => gaussianAliasCoeff (k i) (C i) b B)
    (a := fun i => gaussianAliasRate (k i) b B)
    (fun i hi => gaussianAliasCoeff_nonneg (k i) (hC i hi) hB)
    (fun i hi => gaussianAliasRate_pos (k i) hB (hk i hi)) hB hu
    (fun x => (hf x).trans (Finset.sum_le_sum fun i hi =>
      polynomialGaussian_le_exp (k i) (hC i hi) hb hB x))
  apply ht.trans_eq
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => gaussianAliasCoeff_cancel (k i) (C i) b hB

end FiniteEnvelope

end

end Fourier
