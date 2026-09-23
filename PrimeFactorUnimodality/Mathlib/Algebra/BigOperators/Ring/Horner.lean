/-
Copyright (c) 2026 Jonas Whidden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonas Whidden
-/
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.List.Range

/-! # List Horner evaluation of finite power sums

Right-sided multiplication preserves the exact coefficient order, so the
identity needs only a semiring, not commutative multiplication. Arbitrary
starting indices allow slices of one shared coefficient array.
-/

namespace List

open Finset

/-- A list Horner fold evaluates the complete finite power sum on a consecutive slice. -/
theorem foldr_horner_range' {R : Type*} [Semiring R]
    (a : ℕ → R) (x : R) (start count : ℕ) :
    ((List.range' start count).map a).foldr (fun c v => c + v * x) 0 =
      ∑ j ∈ Finset.range count, a (start + j) * x ^ j := by
  induction count generalizing start with
  | zero => simp
  | succ count ih =>
    simp only [List.range'_succ, List.map_cons, List.foldr_cons, ih, Finset.sum_range_succ',
      pow_zero, mul_one, Nat.add_zero]
    rw [Finset.sum_mul]
    simp only [pow_succ, mul_assoc]
    have he : (∑ j ∈ Finset.range count, a (start + 1 + j) * (x ^ j * x)) =
        ∑ j ∈ Finset.range count, a (start + (j + 1)) * (x ^ j * x) := by
      apply Finset.sum_congr rfl
      intro j hj
      rw [show start + 1 + j = start + (j + 1) by omega]
    rw [he]
    exact add_comm _ _

end List
