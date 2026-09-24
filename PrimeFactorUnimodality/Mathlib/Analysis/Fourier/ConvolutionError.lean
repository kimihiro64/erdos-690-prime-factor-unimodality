/-
Copyright (c) 2026 Jonas Whidden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonas Whidden
-/
import PrimeFactorUnimodality.Mathlib.Analysis.Fourier.CyclicConvolution
import PrimeFactorUnimodality.Mathlib.Analysis.Fourier.DiscretePoisson

/-! # Rounding bounds for shared convolution products

Approximate factors, colliding buckets and accumulation have separate error
budgets. The normalized inverse transform cancels the length factor on a
uniform frequency-input error, but retains inverse-transform rounding divided
by the length. No exact numerical transform is assumed.
-/

open Finset

namespace Complex

/-- Local rounded additions telescope, retaining the initial accumulator error. -/
theorem norm_sum_range_sub_accumulated_le (K : ℕ) (a v : ℕ → ℂ) (ε : ℕ → ℝ)
    {δ : ℝ} (hzero : ‖v 0‖ ≤ δ)
    (hstep : ∀ i < K, ‖v i + a i - v (i + 1)‖ ≤ ε i) :
    ‖(∑ i ∈ range K, a i) - v K‖ ≤ δ + ∑ i ∈ range K, ε i := by
  induction K with
  | zero => simpa using hzero
  | succ K ih =>
    have hp := ih (fun i hi => hstep i (Nat.lt_succ_of_lt hi))
    rw [sum_range_succ, sum_range_succ]
    have he : ‖(∑ i ∈ range K, a i) + a K - (v K + a K)‖ ≤
        δ + ∑ i ∈ range K, ε i := by simpa only [add_sub_add_right_eq_sub] using hp
    exact ((norm_sub_le_norm_sub_add_norm_sub _ (v K + a K) _).trans
      (add_le_add he (hstep K (Nat.lt_succ_self K)))).trans_eq (by ring)

/-- A rounded product and one addition per step suffice to enclose the complete product sum. -/
theorem norm_sum_range_mul_sub_accumulated_le (K : ℕ) (p q u v : ℕ → ℂ)
    (μ ε : ℕ → ℝ) {δ : ℝ} (hzero : ‖v 0‖ ≤ δ)
    (hprod : ∀ i < K, ‖p i * q i - u i‖ ≤ μ i)
    (hstep : ∀ i < K, ‖v i + u i - v (i + 1)‖ ≤ ε i) :
    ‖(∑ i ∈ range K, p i * q i) - v K‖ ≤ δ + ∑ i ∈ range K, (μ i + ε i) := by
  apply norm_sum_range_sub_accumulated_le K _ v _ hzero
  intro i hi
  have hp : ‖v i + p i * q i - (v i + u i)‖ ≤ μ i := by
    simpa only [add_sub_add_left_eq_sub] using hprod i hi
  exact (norm_sub_le_norm_sub_add_norm_sub _ (v i + u i) _).trans
    (add_le_add hp (hstep i hi))

/-- Product error in terms of caps on the approximate, not exact, factors. -/
theorem norm_mul_sub_mul_le_of_approx_bounds {a b p q : ℂ} {α β A B : ℝ}
    (ha : ‖a - p‖ ≤ α) (hb : ‖b - q‖ ≤ β) (hp : ‖p‖ ≤ A) (hq : ‖q‖ ≤ B) :
    ‖a * b - p * q‖ ≤ α * (B + β) + A * β := by
  have hα : 0 ≤ α := (norm_nonneg _).trans ha
  have hβ : 0 ≤ β := (norm_nonneg _).trans hb
  have hb' : ‖b‖ ≤ B + β := by
    calc
      ‖b‖ = ‖q + (b - q)‖ := by congr 1; ring
      _ ≤ ‖q‖ + ‖b - q‖ := norm_add_le _ _
      _ ≤ B + β := add_le_add hq hb
  calc
    ‖a * b - p * q‖ = ‖(a - p) * b + p * (b - q)‖ := by congr 1; ring
    _ ≤ ‖a - p‖ * ‖b‖ + ‖p‖ * ‖b - q‖ := by
      simpa only [norm_mul] using norm_add_le ((a - p) * b) (p * (b - q))
    _ ≤ α * (B + β) + A * β := add_le_add
      ((mul_le_mul_of_nonneg_right ha (norm_nonneg _)).trans
        (mul_le_mul_of_nonneg_left hb' hα))
      ((mul_le_mul_of_nonneg_left hb (norm_nonneg _)).trans
        (mul_le_mul_of_nonneg_right hp hβ))

/-- All products are summed before rounding; the accumulation error is retained once. -/
theorem norm_sum_mul_sub_rounded_le {ι : Type*} (s : Finset ι)
    {a b p q : ι → ℂ} {α β A B : ι → ℝ} {v : ℂ} {δ : ℝ}
    (ha : ∀ i ∈ s, ‖a i - p i‖ ≤ α i) (hb : ∀ i ∈ s, ‖b i - q i‖ ≤ β i)
    (hp : ∀ i ∈ s, ‖p i‖ ≤ A i) (hq : ∀ i ∈ s, ‖q i‖ ≤ B i)
    (hv : ‖(∑ i ∈ s, p i * q i) - v‖ ≤ δ) :
    ‖(∑ i ∈ s, a i * b i) - v‖ ≤
      (∑ i ∈ s, (α i * (B i + β i) + A i * β i)) + δ := by
  apply (norm_sub_le_norm_sub_add_norm_sub _ (∑ i ∈ s, p i * q i) _).trans
  apply add_le_add _ hv
  rw [← sum_sub_distrib]
  exact (norm_sum_le _ _).trans (sum_le_sum fun i hi =>
    norm_mul_sub_mul_le_of_approx_bounds (ha i hi) (hb i hi) (hp i hi) (hq i hi))

end Complex

namespace ZMod

noncomputable section

variable {N : ℕ}

/-- Bucket error counts every colliding input and then the bucket's accumulation rounding. -/
theorem norm_bucketCoefficients_sub_rounded_le {ι : Type*} (s : Finset ι)
    (bin : ι → ZMod N) {a p : ι → ℂ} {ε : ι → ℝ} {b : ℂ} {δ : ℝ}
    (ha : ∀ i ∈ s, ‖a i - p i‖ ≤ ε i) (l : ZMod N)
    (hb : ‖bucketCoefficients s bin p l - b‖ ≤ δ) :
    ‖bucketCoefficients s bin a l - b‖ ≤
      (∑ i ∈ s.filter (fun i => bin i = l), ε i) + δ := by
  apply (norm_sub_le_norm_sub_add_norm_sub _ (bucketCoefficients s bin p l) _).trans
  apply add_le_add _ hb
  simp only [bucketCoefficients, ← sum_sub_distrib]
  exact (norm_sum_le _ _).trans (sum_le_sum fun i hi => ha i (mem_filter.mp hi).1)

/-- A normalized inverse DFT does not amplify uniform frequency-input errors. -/
theorem norm_inv_dft_sub_rounded_le [NeZero N] {a b : ZMod N → ℂ} {ε δ : ℝ} {z : ℂ}
    (ha : ∀ l, ‖a l - b l‖ ≤ ε) (j : ZMod N) (hz : ‖dft b (-j) - z‖ ≤ δ) :
    ‖(N : ℂ)⁻¹ * dft a (-j) - (N : ℂ)⁻¹ * z‖ ≤ ε + δ / (N : ℝ) := by
  have hN : (0 : ℝ) < N := Nat.cast_pos.mpr (NeZero.pos N)
  have he : ‖dft a (-j) - z‖ ≤ (N : ℝ) * ε + δ :=
    (norm_sub_le_norm_sub_add_norm_sub _ (dft b (-j)) _).trans
      (add_le_add (norm_dft_sub_le ha (-j)) hz)
  rw [← mul_sub, norm_mul, norm_inv, Complex.norm_natCast]
  calc
    (N : ℝ)⁻¹ * ‖dft a (-j) - z‖ ≤ (N : ℝ)⁻¹ * ((N : ℝ) * ε + δ) :=
      mul_le_mul_of_nonneg_left he (inv_nonneg.mpr hN.le)
    _ = ε + δ / (N : ℝ) := by field_simp

end

end ZMod
