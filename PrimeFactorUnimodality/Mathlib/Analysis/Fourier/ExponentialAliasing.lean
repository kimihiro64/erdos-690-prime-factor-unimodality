/-
Copyright (c) 2026 Jonas Whidden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonas Whidden
-/
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Topology.Algebra.InfiniteSum.NatInt

/-! # Periodization errors from finite exponential majorants

A finite sum of decaying exponentials controls both tails of every lattice
translate in its central cell. Exact geometric summation gives an explicit
aliasing bound, together with summability of the actual periodization.
-/

open Finset

namespace Fourier

/-- Exact sum of the exponential majorant on half-offset positive lattice points. -/
theorem hasSum_exp_half_lattice {a A : ℝ} (ha : 0 < a) (hA : 0 < A) :
    HasSum (fun n : ℕ => Real.exp (-a * (((n : ℝ) + 1 / 2) * A)))
      (Real.exp (-a * A / 2) / (1 - Real.exp (-a * A))) := by
  have hr : Real.exp (-a * A) < 1 := Real.exp_lt_one_iff.mpr (by nlinarith)
  convert (hasSum_geometric_of_lt_one (Real.exp_pos _).le hr).mul_left
    (Real.exp (-a * A / 2)) using 1
  · ext n
    rw [← Real.exp_nat_mul, ← Real.exp_add]
    congr 1
    ring
  · rw [div_eq_mul_inv]

section FiniteEnvelope

variable {ι E : Type*} [NormedAddCommGroup E] [CompleteSpace E]
    {s : Finset ι} {c a : ι → ℝ} {f : ℝ → E} {A u : ℝ}

private theorem hasSum_finite_exp_half_lattice (ha : ∀ i ∈ s, 0 < a i) (hA : 0 < A) :
    HasSum (fun n : ℕ => ∑ i ∈ s, c i * Real.exp (-a i * (((n : ℝ) + 1 / 2) * A)))
      (∑ i ∈ s, c i * (Real.exp (-a i * A / 2) / (1 - Real.exp (-a i * A)))) :=
  hasSum_sum fun i hi => (hasSum_exp_half_lattice (ha i hi) hA).mul_left (c i)

omit [CompleteSpace E] in
private theorem norm_le_finite_exp_half_lattice (hc : ∀ i ∈ s, 0 ≤ c i)
    (ha : ∀ i ∈ s, 0 < a i)
    (hf : ∀ v, ‖f v‖ ≤ ∑ i ∈ s, c i * Real.exp (-a i * |v|))
    (n : ℕ) (v : ℝ) (hv : ((n : ℝ) + 1 / 2) * A ≤ |v|) :
    ‖f v‖ ≤ ∑ i ∈ s, c i * Real.exp (-a i * (((n : ℝ) + 1 / 2) * A)) := by
  apply (hf v).trans
  apply sum_le_sum
  intro i hi
  apply mul_le_mul_of_nonneg_left _ (hc i hi)
  apply Real.exp_le_exp.mpr
  exact mul_le_mul_of_nonpos_left hv (neg_nonpos.mpr (ha i hi).le)

/-- Both omitted tails really converge under the finite exponential bound. -/
theorem summable_lattice_tails_of_finite_exp_bound (hc : ∀ i ∈ s, 0 ≤ c i)
    (ha : ∀ i ∈ s, 0 < a i) (hA : 0 < A) (hu : |u| ≤ A / 2)
    (hf : ∀ v, ‖f v‖ ≤ ∑ i ∈ s, c i * Real.exp (-a i * |v|)) :
    Summable (fun n : ℕ => f (u + ((n : ℝ) + 1) * A)) ∧
      Summable (fun n : ℕ => f (u - ((n : ℝ) + 1) * A)) := by
  have hs := (hasSum_finite_exp_half_lattice (c := c) ha hA).summable
  constructor
  · apply hs.of_norm_bounded
    intro n
    apply norm_le_finite_exp_half_lattice hc ha hf
    linarith [(abs_le.mp hu).1, le_abs_self (u + ((n : ℝ) + 1) * A)]
  · apply hs.of_norm_bounded
    intro n
    apply norm_le_finite_exp_half_lattice hc ha hf
    linarith [(abs_le.mp hu).2, neg_le_abs (u - ((n : ℝ) + 1) * A)]

/-- The complete integer periodization is summable on its central cell. -/
theorem summable_lattice_of_finite_exp_bound (hc : ∀ i ∈ s, 0 ≤ c i)
    (ha : ∀ i ∈ s, 0 < a i) (hA : 0 < A) (hu : |u| ≤ A / 2)
    (hf : ∀ v, ‖f v‖ ≤ ∑ i ∈ s, c i * Real.exp (-a i * |v|)) :
    Summable (fun n : ℤ => f (u + (n : ℝ) * A)) := by
  obtain ⟨hp, hn⟩ := summable_lattice_tails_of_finite_exp_bound hc ha hA hu hf
  apply Summable.of_nat_of_neg_add_one
  · exact (summable_nat_add_iff 1).mp (by simpa using hp)
  · simpa only [Int.cast_neg, Int.cast_add, Int.cast_natCast, Int.cast_one,
      neg_mul, sub_eq_add_neg] using hn

/-- Removing the central term leaves at most the exactly summed two-sided majorant. -/
theorem norm_periodization_sub_le_of_finite_exp_bound (hc : ∀ i ∈ s, 0 ≤ c i)
    (ha : ∀ i ∈ s, 0 < a i) (hA : 0 < A) (hu : |u| ≤ A / 2)
    (hf : ∀ v, ‖f v‖ ≤ ∑ i ∈ s, c i * Real.exp (-a i * |v|)) :
    ‖(∑' n : ℤ, f (u + (n : ℝ) * A)) - f u‖ ≤
      2 * ∑ i ∈ s, c i * (Real.exp (-a i * A / 2) / (1 - Real.exp (-a i * A))) := by
  obtain ⟨hp, hn⟩ := summable_lattice_tails_of_finite_exp_bound hc ha hA hu hf
  have hp₀ : Summable (fun n : ℕ => f (u + (n : ℝ) * A)) :=
    (summable_nat_add_iff 1).mp (by simpa using hp)
  have hn' : Summable (fun n : ℕ => f (u + ((-(n + 1) : ℤ) : ℝ) * A)) := by
    simpa only [Int.cast_neg, Int.cast_add, Int.cast_natCast, Int.cast_one,
      neg_mul, sub_eq_add_neg] using hn
  rw [tsum_of_nat_of_neg_add_one (f := fun n : ℤ => f (u + (n : ℝ) * A))
    (by simpa only [Int.cast_natCast] using hp₀) hn']
  simp only [Int.cast_natCast]
  rw [hp₀.tsum_eq_zero_add]
  conv_lhs =>
    simp only [Nat.cast_zero, zero_mul, add_zero, Nat.cast_add, Nat.cast_one,
      Int.cast_neg, Int.cast_add, Int.cast_natCast, Int.cast_one, neg_mul]
  have he : f u + (∑' n : ℕ, f (u + ((n : ℝ) + 1) * A)) +
      (∑' n : ℕ, f (u + -(((n : ℝ) + 1) * A))) - f u =
      (∑' n : ℕ, f (u + ((n : ℝ) + 1) * A)) +
        (∑' n : ℕ, f (u + -(((n : ℝ) + 1) * A))) := by abel
  rw [he]
  apply (norm_add_le _ _).trans
  rw [two_mul]
  apply add_le_add
  · apply tsum_of_norm_bounded (hasSum_finite_exp_half_lattice (c := c) ha hA)
    intro n
    apply norm_le_finite_exp_half_lattice hc ha hf
    linarith [(abs_le.mp hu).1, le_abs_self (u + ((n : ℝ) + 1) * A)]
  · apply tsum_of_norm_bounded (hasSum_finite_exp_half_lattice (c := c) ha hA)
    intro n
    apply norm_le_finite_exp_half_lattice hc ha hf
    linarith [(abs_le.mp hu).2, neg_le_abs (u + -(((n : ℝ) + 1) * A))]

end FiniteEnvelope

end Fourier
