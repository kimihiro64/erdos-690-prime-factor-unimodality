/-
Copyright (c) 2026 Jonas Whidden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonas Whidden
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import PrimeFactorUnimodality.Mathlib.Analysis.SpecialFunctions.Complex.GroupedRounding

/-! # Shared frequency groups for finite Dirichlet polynomials

Separate the base height from a real shift, round scaled logarithmic
frequencies to integers, and reuse one family of moments on a whole window.
The bounds retain every term and include both Taylor and rounding errors.
-/

namespace Complex

noncomputable section

open Finset

/-- The scaled logarithmic frequency in a finite Dirichlet sum. -/
def dirichletFrequency (R : ℝ) (n : ℕ) : ℝ := -R * Real.log n

/-- Nearest-integer assignment of the scaled frequency. -/
def dirichletFrequencyBin (R : ℝ) (n : ℕ) : ℤ := ⌊dirichletFrequency R n + 1 / 2⌋

/-- Only groups containing an actual summand need stored coefficients. -/
def dirichletFrequencyBins (S : Finset ℕ) (R : ℝ) : Finset ℤ :=
  S.image (dirichletFrequencyBin R)

/-- A group coefficient shared by all evaluation points in the normalized window. -/
def dirichletGroupMoment (S : Finset ℕ) (s : ℂ) (R : ℝ) (b : ℤ) (j : ℕ) : ℂ :=
  expSumMoment (S.filter (fun n => dirichletFrequencyBin R n = b))
    (fun n => 1 / (n : ℂ) ^ s) (fun n => dirichletFrequency R n - b) j

/-- The grouped approximation uses the same base-point moments throughout the window. -/
def dirichletGroupedApprox (S : Finset ℕ) (s : ℂ) (R : ℝ) (m : ℕ) (v : ℝ) : ℂ :=
  groupedExpPolynomial S (dirichletFrequencyBins S R) (dirichletFrequencyBin R)
    (fun n => 1 / (n : ℂ) ^ s) (dirichletFrequency R) (fun b : ℤ => b) m v

/-- Moving the height of a positive Dirichlet atom multiplies it by an exact unit phase. -/
theorem natCpow_inv_shift (n : ℕ) (hn : 0 < n) (s : ℂ) (R v : ℝ) :
    1 / (n : ℂ) ^ (s + (R * v : ℝ) * I) =
      (1 / (n : ℂ) ^ s) * exp (I * ((v * dirichletFrequency R n : ℝ) : ℂ)) := by
  have hn₀ : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have he : -(s + (R * v : ℝ) * I) = -s + (-(R * v : ℝ) : ℂ) * I := by
    push_cast
    ring
  have hp : (n : ℂ) ^ ((-(R * v : ℝ) : ℂ) * I) =
      exp (I * ((v * dirichletFrequency R n : ℝ) : ℂ)) := by
    rw [cpow_def_of_ne_zero hn₀]
    congr 1
    rw [← ofReal_natCast n, ← ofReal_log (Nat.cast_nonneg n)]
    simp only [dirichletFrequency, ofReal_mul, ofReal_neg]
    ring
  calc
    _ = (n : ℂ) ^ (-s + (-(R * v : ℝ) : ℂ) * I) := by rw [one_div, ← cpow_neg, he]
    _ = (n : ℂ) ^ (-s) * (n : ℂ) ^ ((-(R * v : ℝ) : ℂ) * I) := cpow_add _ _ hn₀
    _ = _ := by simp only [cpow_neg, hp, one_div]

/-- Positive Dirichlet atoms have norm at most one in the closed right half-plane. -/
theorem norm_natCpow_inv_le_one {n : ℕ} (hn : 0 < n) {s : ℂ} (hs : 0 ≤ s.re) :
    ‖1 / (n : ℂ) ^ s‖ ≤ 1 := by
  rw [norm_div, norm_one, norm_natCast_cpow_of_pos hn]
  have hp : (1 : ℝ) ≤ (n : ℝ) ^ s.re :=
    Real.one_le_rpow (by exact_mod_cast hn) hs
  exact (one_div_le_one_div_of_le (by norm_num) hp).trans_eq (by norm_num)

/-- The positive-index coefficient mass admits a simple height-independent bound. -/
theorem sum_norm_natCpow_inv_le_card (S : Finset ℕ) (hS : ∀ n ∈ S, 0 < n)
    {s : ℂ} (hs : 0 ≤ s.re) : (∑ n ∈ S, ‖1 / (n : ℂ) ^ s‖) ≤ S.card := by
  calc
    _ ≤ ∑ _n ∈ S, (1 : ℝ) := sum_le_sum (fun n hn => norm_natCpow_inv_le_one (hS n hn) hs)
    _ = _ := by simp

/-- The full finite Dirichlet sum has a uniform geometric grouping error. -/
theorem norm_dirichlet_sum_sub_grouped_le (S : Finset ℕ) (hS : ∀ n ∈ S, 0 < n)
    {s : ℂ} (hs : 0 ≤ s.re) (R : ℝ) {v : ℝ} (hv : |v| ≤ 1) (m : ℕ) :
    ‖(∑ n ∈ S, 1 / (n : ℂ) ^ (s + (R * v : ℝ) * I)) -
      dirichletGroupedApprox S s R m v‖ ≤
      (S.card : ℝ) * ((1 / 2 : ℝ) ^ m * Real.exp (1 / 2)) := by
  have he : (∑ n ∈ S, 1 / (n : ℂ) ^ (s + (R * v : ℝ) * I)) =
      ∑ n ∈ S, (1 / (n : ℂ) ^ s) * exp (I * ((v * dirichletFrequency R n : ℝ) : ℂ)) :=
    sum_congr rfl (fun n hn => natCpow_inv_shift n (hS n hn) s R v)
  rw [he]
  exact (norm_expSum_sub_nearestGrouped_le S (fun n => 1 / (n : ℂ) ^ s)
    (dirichletFrequency R) hv m).trans
    (mul_le_mul_of_nonneg_right (sum_norm_natCpow_inv_le_card S hS hs) (by positivity))

/-- Stored group moments and phases give a complete rounded bound for every point in the window. -/
theorem norm_dirichlet_sum_sub_rounded_with_centers_le {κ : Type*} [DecidableEq κ]
    (S : Finset ℕ) (hS : ∀ n ∈ S, 0 < n) {s : ℂ} (hs : 0 ≤ s.re)
    (R : ℝ) (B : Finset κ) (bin : ℕ → κ) (c : κ → ℝ)
    (hbin : ∀ n ∈ S, bin n ∈ B) {A v : ℝ} (hA : 0 ≤ A) (hv : |v| ≤ 1)
    (hres : ∀ n ∈ S, |dirichletFrequency R n - c (bin n)| ≤ A)
    (m : ℕ) (a : κ → ℕ → ℂ) (p : κ → ℂ) (ε : κ → ℕ → ℝ) (δ : κ → ℝ)
    (ha : ∀ b ∈ B, ∀ j ∈ range m,
      ‖expSumMoment (S.filter (fun n => bin n = b)) (fun n => 1 / (n : ℂ) ^ s)
        (fun n => dirichletFrequency R n - c b) j - a b j‖ ≤ ε b j)
    (hp : ∀ b ∈ B, ‖exp (I * ((v * c b : ℝ) : ℂ)) - p b‖ ≤ δ b) :
    ‖(∑ n ∈ S, 1 / (n : ℂ) ^ (s + (R * v : ℝ) * I)) -
      ∑ b ∈ B, p b * ∑ j ∈ range m, a b j * (v : ℂ) ^ j‖ ≤
      (S.card : ℝ) * (A ^ m * Real.exp A) +
        ∑ b ∈ B, ((∑ j ∈ range m, ε b j * |v| ^ j) +
          ‖∑ j ∈ range m, a b j * (v : ℂ) ^ j‖ * δ b) := by
  have he : (∑ n ∈ S, 1 / (n : ℂ) ^ (s + (R * v : ℝ) * I)) =
      ∑ n ∈ S, (1 / (n : ℂ) ^ s) * exp (I * ((v * dirichletFrequency R n : ℝ) : ℂ)) :=
    sum_congr rfl (fun n hn => natCpow_inv_shift n (hS n hn) s R v)
  rw [he]
  have hb := norm_expSum_sub_roundedGrouped_le S B bin (fun n => 1 / (n : ℂ) ^ s)
    (dirichletFrequency R) c hbin hA (fun n hn => by
      rw [abs_mul]
      exact (mul_le_mul hv (hres n hn) (abs_nonneg _) (by norm_num)).trans_eq (one_mul A))
    m a p ε δ ha hp
  have hm : (∑ n ∈ S, ‖1 / (n : ℂ) ^ s‖) * (A ^ m * Real.exp A) ≤
      (S.card : ℝ) * (A ^ m * Real.exp A) :=
    mul_le_mul_of_nonneg_right (sum_norm_natCpow_inv_le_card S hS hs) (by positivity)
  exact hb.trans (add_le_add hm le_rfl)

/-- Nearest-integer centers are a convenience specialization; explicit bins can be used instead. -/
theorem norm_dirichlet_sum_sub_roundedGrouped_le
    (S : Finset ℕ) (hS : ∀ n ∈ S, 0 < n) {s : ℂ} (hs : 0 ≤ s.re)
    (R : ℝ) {v : ℝ} (hv : |v| ≤ 1) (m : ℕ)
    (a : ℤ → ℕ → ℂ) (p : ℤ → ℂ) (ε : ℤ → ℕ → ℝ) (δ : ℤ → ℝ)
    (ha : ∀ b ∈ dirichletFrequencyBins S R, ∀ j ∈ range m,
      ‖dirichletGroupMoment S s R b j - a b j‖ ≤ ε b j)
    (hp : ∀ b ∈ dirichletFrequencyBins S R,
      ‖exp (I * ((v * b : ℝ) : ℂ)) - p b‖ ≤ δ b) :
    ‖(∑ n ∈ S, 1 / (n : ℂ) ^ (s + (R * v : ℝ) * I)) -
      ∑ b ∈ dirichletFrequencyBins S R, p b * ∑ j ∈ range m, a b j * (v : ℂ) ^ j‖ ≤
      (S.card : ℝ) * ((1 / 2 : ℝ) ^ m * Real.exp (1 / 2)) +
        ∑ b ∈ dirichletFrequencyBins S R, ((∑ j ∈ range m, ε b j * |v| ^ j) +
          ‖∑ j ∈ range m, a b j * (v : ℂ) ^ j‖ * δ b) := by
  exact (norm_sub_le_norm_sub_add_norm_sub _ (dirichletGroupedApprox S s R m v) _).trans
    (add_le_add (norm_dirichlet_sum_sub_grouped_le S hS hs R hv m)
      (norm_groupedExpPolynomial_sub_rounded_le S (dirichletFrequencyBins S R)
        (dirichletFrequencyBin R) (fun n => 1 / (n : ℂ) ^ s) (dirichletFrequency R)
        (fun b : ℤ => b) m v a p ε δ ha hp))

end

end Complex
