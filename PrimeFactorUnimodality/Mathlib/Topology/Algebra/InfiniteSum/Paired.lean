/-
Copyright (c) 2026 Jonas Whidden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonas Whidden
-/
import Mathlib.Tactic.Linarith
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.Instances.Real.Lemmas

/-! # Retaining one pair in a summable series with nonnegative pairs

Individual terms may have either sign. Apply the existing finite-subsum
bound to the nonnegative symmetrized series and reindex by the involution.
The retained orbit must have two distinct elements; fixed points are not
counted twice. All infinite-sum bookkeeping uses Mathlib's summability API.
-/

/-- Retain a two-element orbit when all involution-paired terms are nonnegative. -/
theorem Summable.pair_le_tsum_of_involution {ι : Type*} {f : ι → ℝ} (hf : Summable f)
    (e : Equiv.Perm ι) (he : Function.Involutive e)
    (hpair : ∀ i, 0 ≤ f i + f (e i)) (i : ι) (hne : i ≠ e i) :
    f i + f (e i) ≤ ∑' j, f j := by
  classical
  have hsum := hf.add (hf.comp_injective e.injective)
  have h := hsum.sum_le_tsum {i, e i} (fun j _ => hpair j)
  simp only [Finset.sum_pair hne] at h
  have heq := hf.tsum_add (hf.comp_injective e.injective)
  simp only [Function.comp_apply] at heq
  rw [e.tsum_eq f] at heq
  rw [heq, he i] at h
  linarith
