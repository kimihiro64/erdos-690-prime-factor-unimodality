/-
Copyright (c) 2026 Jonas Whidden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonas Whidden
-/
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Data.Nat.Dist
import Mathlib.Tactic.Ring

/-! # Nonnegative cosine polynomials from finite autocorrelations

Group the square of a finite Fourier sum by the absolute difference of its
natural frequencies. This gives a cosine polynomial nonnegative at every
real phase, even when the generating coefficients have mixed signs.
The zero-frequency coefficient counts each diagonal once; positive
frequencies count both orientations. Nonnegativity of the individual
cosine coefficients is a separate property, not a consequence of this identity.
-/

namespace Real

open Finset

noncomputable section

/-- The cosine coefficient obtained by grouping ordered pairs of natural frequencies. -/
def cosineAutocorrelationCoeff (s : Finset ℕ) (c : ℕ → ℝ) (k : ℕ) : ℝ :=
  ∑ i ∈ s, ∑ j ∈ s, if Nat.dist i j = k then c i * c j else 0

/-- The constant coefficient is the sum of squares of the generating coefficients. -/
@[simp]
theorem cosineAutocorrelationCoeff_zero (s : Finset ℕ) (c : ℕ → ℝ) :
    cosineAutocorrelationCoeff s c 0 = ∑ i ∈ s, c i ^ 2 := by
  unfold cosineAutocorrelationCoeff
  apply sum_congr rfl
  intro i hi
  have hd (j : ℕ) : Nat.dist i j = 0 ↔ i = j :=
    ⟨Nat.eq_of_dist_eq_zero, Nat.dist_eq_zero⟩
  simp_rw [hd]
  simp [hi, sq]

/-- At a positive frequency the two pair orientations give twice the usual autocorrelation.
This linear-sized formula avoids evaluating the defining double sum. -/
theorem cosineAutocorrelationCoeff_range_pos (n : ℕ) (c : ℕ → ℝ) {k : ℕ} (hk : 0 < k) :
    cosineAutocorrelationCoeff (range n) c k =
      2 * ∑ i ∈ range (n - k), c i * c (i + k) := by
  have hsplit (i j : ℕ) :
      (if Nat.dist i j = k then c i * c j else 0) =
        (if i + k = j then c i * c j else 0) +
          (if j + k = i then c j * c i else 0) := by
    have hd : Nat.dist i j = k ↔ i + k = j ∨ j + k = i := by
      unfold Nat.dist
      omega
    simp only [hd]
    by_cases hij : i + k = j
    · have hji : j + k ≠ i := by omega
      simp [hij, hji]
    · by_cases hji : j + k = i <;> simp [hij, hji, mul_comm]
  unfold cosineAutocorrelationCoeff
  simp_rw [hsplit, sum_add_distrib]
  rw [sum_comm (f := fun i j => if j + k = i then c j * c i else 0)]
  rw [← two_mul]
  congr 1
  simp only [sum_ite_eq, mem_range]
  calc
    (∑ i ∈ range n, if i + k < n then c i * c (i + k) else 0) =
        ∑ i ∈ range (n - k), if i + k < n then c i * c (i + k) else 0 := by
      symm
      apply sum_subset (range_mono (Nat.sub_le n k))
      intro i hi hin
      have hn : ¬i + k < n := by simp only [mem_range] at hi hin; omega
      simp [hn]
    _ = ∑ i ∈ range (n - k), c i * c (i + k) := by
      apply sum_congr rfl
      intro i hi
      have hn : i + k < n := by simp only [mem_range] at hi; omega
      simp [hn]

/-- The cosine difference kernel is the sum of two real squares. -/
theorem sum_mul_cos_sub_eq_sq_add_sq {ι : Type*} (s : Finset ι) (c x : ι → ℝ) :
    (∑ i ∈ s, ∑ j ∈ s, c i * c j * cos (x i - x j)) =
      (∑ i ∈ s, c i * cos (x i)) ^ 2 + (∑ i ∈ s, c i * sin (x i)) ^ 2 := by
  simp_rw [cos_sub, mul_add, sum_add_distrib, sq, sum_mul_sum]
  congr 1 <;> apply sum_congr rfl <;> intro i hi <;> apply sum_congr rfl <;>
    intro j hj <;> ring

private theorem cos_nat_dist_mul (i j : ℕ) (u : ℝ) :
    cos ((Nat.dist i j : ℕ) * u) = cos ((i : ℝ) * u - (j : ℝ) * u) := by
  rcases le_total i j with hij | hji
  · rw [Nat.dist_eq_sub_of_le hij, Nat.cast_sub hij, sub_mul]
    rw [← neg_sub ((i : ℝ) * u), cos_neg]
  · rw [Nat.dist_eq_sub_of_le_right hji, Nat.cast_sub hji, sub_mul]

/-- Grouping by frequency difference gives the exact sum-of-squares identity. -/
theorem sum_cosineAutocorrelationCoeff_mul_cos (s : Finset ℕ) (c : ℕ → ℝ)
    (n : ℕ) (hs : ∀ i ∈ s, i ≤ n) (u : ℝ) :
    (∑ k ∈ range (n + 1), cosineAutocorrelationCoeff s c k * cos ((k : ℝ) * u)) =
      (∑ i ∈ s, c i * cos ((i : ℝ) * u)) ^ 2 +
        (∑ i ∈ s, c i * sin ((i : ℝ) * u)) ^ 2 := by
  unfold cosineAutocorrelationCoeff
  simp_rw [sum_mul]
  rw [sum_comm]
  conv_lhs => arg 2; ext i; rw [sum_comm]
  have hgroup : ∀ i ∈ s, ∀ j ∈ s,
      (∑ k ∈ range (n + 1), (if Nat.dist i j = k then c i * c j else 0) *
        cos ((k : ℝ) * u)) = c i * c j * cos ((i : ℝ) * u - (j : ℝ) * u) := by
    intro i hi j hj
    have hdist : Nat.dist i j ∈ range (n + 1) := by
      have hi' := hs i hi
      have hj' := hs j hj
      simp only [mem_range, Nat.dist]
      omega
    rw [sum_eq_single_of_mem (Nat.dist i j) hdist]
    · simp only [ite_true, cos_nat_dist_mul]
    · intro k hk hki
      simp [Ne.symm hki]
  simp_rw [sum_congr rfl fun i hi => sum_congr rfl fun j hj => hgroup i hi j hj]
  exact sum_mul_cos_sub_eq_sq_add_sq s c (fun i => (i : ℝ) * u)

/-- Autocorrelation gives global phase nonnegativity, with no sign condition on the input. -/
theorem sum_cosineAutocorrelationCoeff_mul_cos_nonneg (s : Finset ℕ) (c : ℕ → ℝ)
    (n : ℕ) (hs : ∀ i ∈ s, i ≤ n) (u : ℝ) :
    0 ≤ ∑ k ∈ range (n + 1), cosineAutocorrelationCoeff s c k * cos ((k : ℝ) * u) := by
  rw [sum_cosineAutocorrelationCoeff_mul_cos s c n hs u]
  exact add_nonneg (sq_nonneg _) (sq_nonneg _)

/-- The sum of the cosine coefficients is the square of the sum of the input coefficients. -/
theorem sum_cosineAutocorrelationCoeff (s : Finset ℕ) (c : ℕ → ℝ)
    (n : ℕ) (hs : ∀ i ∈ s, i ≤ n) :
    (∑ k ∈ range (n + 1), cosineAutocorrelationCoeff s c k) = (∑ i ∈ s, c i) ^ 2 := by
  simpa using sum_cosineAutocorrelationCoeff_mul_cos s c n hs 0

end

end Real
