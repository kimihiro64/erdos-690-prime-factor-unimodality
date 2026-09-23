/-
Copyright (c) 2026 Jonas Whidden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonas Whidden
-/
import Mathlib.Algebra.BigOperators.Group.List.Basic

/-! # Shared array accumulation of sparse coefficients

Each sparse row performs one array update. Repeated indices add their
coefficients, so aliasing does not require filtering the full input once
per output. The entry theorem is independent of row order or uniqueness.
-/

namespace Vector

variable {R : Type*} [AddCommMonoid R] {N : ℕ}

/-- Tail-recursive sparse accumulation; every transition input is used once. -/
def scatterAdd (a : Vector R N) : List (Fin N × R) → Vector R N
  | [] => a
  | (i, x) :: rows => scatterAdd (a.set i.val (a[i.val] + x)) rows

/-- An output is the original entry plus all matching sparse coefficients. -/
theorem scatterAdd_get (a : Vector R N) (rows : List (Fin N × R)) (k : Fin N) :
    (scatterAdd a rows)[k.val] =
      a[k.val] + (rows.map (fun p => if p.1 = k then p.2 else 0)).sum := by
  induction rows generalizing a with
  | nil => simp [scatterAdd]
  | cons p rows ih =>
    rcases p with ⟨i, x⟩
    rw [scatterAdd, ih]
    by_cases h : i = k
    · subst i
      simp [_root_.add_assoc]
    · have hv : i.val ≠ k.val := fun he => h (Fin.ext he)
      simp [hv, h]

/-- Appending chunks composes their updates without revisiting earlier rows. -/
theorem scatterAdd_append (a : Vector R N) (xs ys : List (Fin N × R)) :
    scatterAdd a (xs ++ ys) = scatterAdd (scatterAdd a xs) ys := by
  induction xs generalizing a with
  | nil => rfl
  | cons p xs ih => exact ih _

end Vector
