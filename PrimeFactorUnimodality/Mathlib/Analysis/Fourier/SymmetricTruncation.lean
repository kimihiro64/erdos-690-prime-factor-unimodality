/-
Copyright (c) 2026 Jonas Whidden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonas Whidden
-/
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Tactic.Abel
import Mathlib.Topology.Algebra.InfiniteSum.NatInt

/-! # Symmetric finite truncation of an absolutely convergent integer series

The retained indices are exactly `-M` through `M`, with zero included once.
Both omitted tails start at `M+1`, including the boundary case `M=0`.
-/

open Finset

namespace Fourier

noncomputable section

/-- The symmetric integer sum, represented by two finite natural-index ranges. -/
def symmetricSum {E : Type*} [AddCommMonoid E] (f : ℤ → E) (M : ℕ) : E :=
  (∑ n ∈ range (M + 1), f n) + ∑ n ∈ range M, f (-(n + 1))

/-- A common summable majorant for the two omitted tails bounds finite truncation. -/
theorem norm_tsum_sub_symmetricSum_le {E : Type*} [NormedAddCommGroup E] [CompleteSpace E]
    {f : ℤ → E} (hf : Summable f) (M : ℕ) {g : ℕ → ℝ} {S : ℝ} (hg : HasSum g S)
    (hp : ∀ n : ℕ, ‖f (n + M + 1)‖ ≤ g n)
    (hn : ∀ n : ℕ, ‖f (-(n + M + 1))‖ ≤ g n) :
    ‖(∑' n : ℤ, f n) - symmetricSum f M‖ ≤ 2 * S := by
  have hs₀ : Summable (fun n : ℕ => f n) := hf.comp_injective Nat.cast_injective
  have hs₁ : Summable (fun n : ℕ => f (-(n + 1))) := hf.comp_injective (by
    intro n m h
    exact_mod_cast add_right_cancel (neg_injective h))
  rw [tsum_of_nat_of_neg_add_one hs₀ hs₁,
    ← hs₀.sum_add_tsum_nat_add (M + 1), ← hs₁.sum_add_tsum_nat_add M, symmetricSum]
  have he : ((∑ n ∈ range (M + 1), f n) + (∑' n : ℕ, f (n + (M + 1))) +
      ((∑ n ∈ range M, f (-(n + 1))) + (∑' n : ℕ, f (-(n + M + 1))))) -
      ((∑ n ∈ range (M + 1), f n) + ∑ n ∈ range M, f (-(n + 1))) =
      (∑' n : ℕ, f (n + (M + 1))) + (∑' n : ℕ, f (-(n + M + 1))) := by abel
  simp only [Nat.cast_add, Nat.cast_one] at *
  rw [he]
  apply (norm_add_le _ _).trans
  rw [two_mul]
  exact add_le_add (tsum_of_norm_bounded hg (fun n => by simpa [add_assoc] using hp n))
    (tsum_of_norm_bounded hg hn)

/-- Finite input uncertainties add over precisely the retained indices. -/
theorem norm_symmetricSum_sub_le {E : Type*} [NormedAddCommGroup E]
    {f g : ℤ → E} {ε : ℤ → ℝ} (M : ℕ)
    (h₀ : ∀ n ∈ range (M + 1), ‖f n - g n‖ ≤ ε n)
    (h₁ : ∀ n ∈ range M, ‖f (-(n + 1)) - g (-(n + 1))‖ ≤ ε (-(n + 1))) :
    ‖symmetricSum f M - symmetricSum g M‖ ≤ symmetricSum ε M := by
  unfold symmetricSum
  rw [show ((∑ n ∈ range (M + 1), f n) + ∑ n ∈ range M, f (-(n + 1))) -
      ((∑ n ∈ range (M + 1), g n) + ∑ n ∈ range M, g (-(n + 1))) =
      ((∑ n ∈ range (M + 1), f n) - ∑ n ∈ range (M + 1), g n) +
        ((∑ n ∈ range M, f (-(n + 1))) - ∑ n ∈ range M, g (-(n + 1))) by abel]
  simp only [← sum_sub_distrib]
  exact (norm_add_le _ _).trans (add_le_add
    ((norm_sum_le _ _).trans (sum_le_sum h₀)) ((norm_sum_le _ _).trans (sum_le_sum h₁)))

end

end Fourier
