/-
Copyright (c) 2026 Jonas Whidden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonas Whidden
-/
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Group.Basic
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! # Array-backed radix-two transforms

Each recursive call materializes its two half-transforms once. Twiddle
powers are generated successively, not recomputed by exponentiation at
every output. Correctness only requires the supplied root to have period
equal to the array length; primitivity is unnecessary.
-/

namespace Fourier

open Finset

variable {R : Type*} [CommSemiring R]

/-- Successive powers, including both the zeroth and final power. -/
def powerTable (w : R) : (n : ℕ) → Vector R (n + 1)
  | 0 => Vector.singleton 1
  | n + 1 => let v := powerTable w n; v.push (v[n] * w)

/-- The linear recurrence produces the usual powers. -/
theorem powerTable_get (w : R) (n : ℕ) (i : Fin (n + 1)) :
    (powerTable w n)[i.val] = w ^ i.val := by
  induction n with
  | zero =>
    simp [powerTable]
  | succ n ih =>
    by_cases h : i.val < n + 1
    · simpa [powerTable, Vector.getElem_push, h] using ih ⟨i.val, h⟩
    · have hi : i.val = n + 1 := by omega
      simp [powerTable, hi, ih ⟨n, by omega⟩, pow_succ]

/-- The even-indexed half of an array of power-of-two length. -/
def evenSamples (n : ℕ) (a : Vector R (2 ^ (n + 1))) : Vector R (2 ^ n) :=
  Vector.ofFn fun i => a[2 * i.val]'(by have := i.isLt; simp only [pow_succ]; omega)

/-- The odd-indexed half of the same array. -/
def oddSamples (n : ℕ) (a : Vector R (2 ^ (n + 1))) : Vector R (2 ^ n) :=
  Vector.ofFn fun i => a[2 * i.val + 1]'(by have := i.isLt; simp only [pow_succ]; omega)

/-- Shared, materialized half-transforms and a linear-size butterfly merge. -/
def radixTwo : (n : ℕ) → R → Vector R (2 ^ n) → Vector R (2 ^ n)
  | 0, _, a => a
  | n + 1, w, a =>
    let u := radixTwo n (w ^ 2) (evenSamples n a)
    let v := radixTwo n (w ^ 2) (oddSamples n a)
    let powers := powerTable w (2 ^ (n + 1))
    Vector.ofFn fun k =>
      u[k.val % (2 ^ n)]'(Nat.mod_lt _ (by positivity)) +
        powers[k.val]'(by have := k.isLt; omega) *
          v[k.val % (2 ^ n)]'(Nat.mod_lt _ (by positivity))

/-- Splitting a finite sum by parity preserves every index exactly once. -/
theorem sum_fin_double (n : ℕ) (f : Fin (n * 2) → R) :
    (∑ i, f i) =
      (∑ i : Fin n, f ⟨2 * i.val, by have := i.isLt; omega⟩) +
        ∑ i : Fin n, f ⟨2 * i.val + 1, by have := i.isLt; omega⟩ := by
  rw [← Equiv.sum_comp finProdFinEquiv]
  rw [Fintype.sum_prod_type]
  simp only [Fin.sum_univ_two, finProdFinEquiv]
  rw [sum_add_distrib]
  congr 1 <;> apply sum_congr rfl <;> intro i hi <;> congr 1 <;> apply Fin.ext <;> simp <;> omega

/-- The array algorithm equals the exact finite Fourier sum at every output. -/
theorem radixTwo_get (n : ℕ) (w : R) (hw : w ^ (2 ^ n) = 1)
    (a : Vector R (2 ^ n)) (k : Fin (2 ^ n)) :
    (radixTwo n w a)[k.val] = ∑ j : Fin (2 ^ n), a[j.val] * w ^ (k.val * j.val) := by
  induction n generalizing w with
  | zero => simp [radixTwo]
  | succ n ih =>
    have hn : 0 < 2 ^ n := by positivity
    have hw' : (w ^ 2) ^ (2 ^ n) = 1 := by
      rw [← pow_mul, Nat.mul_comm, ← pow_succ]
      exact hw
    have hp (j : ℕ) : (w ^ 2) ^ (k.val % (2 ^ n) * j) = w ^ (k.val * (2 * j)) := by
      rw [pow_mul, ← pow_eq_pow_mod k.val hw', ← pow_mul, ← pow_mul]
      congr 1
      ring
    simp only [radixTwo, Vector.getElem_ofFn]
    rw [powerTable_get w _ ⟨k.val, by have := k.isLt; omega⟩,
      ih (w ^ 2) hw' (evenSamples n a) ⟨k.val % (2 ^ n), Nat.mod_lt _ hn⟩,
      ih (w ^ 2) hw' (oddSamples n a) ⟨k.val % (2 ^ n), Nat.mod_lt _ hn⟩]
    simp only [evenSamples, oddSamples, Vector.getElem_ofFn, hp]
    have hs := sum_fin_double (2 ^ n)
      (fun j => a[j.val]'(by have := j.isLt; simpa only [pow_succ] using this) *
        w ^ (k.val * j.val))
    have hs' : (∑ j : Fin (2 ^ (n + 1)), a[j.val] * w ^ (k.val * j.val)) =
        (∑ j : Fin (2 ^ n), a[2 * j.val]'(by have := j.isLt; simp only [pow_succ]; omega) *
          w ^ (k.val * (2 * j.val))) +
        ∑ j : Fin (2 ^ n), a[2 * j.val + 1]'(by have := j.isLt; simp only [pow_succ]; omega) *
          w ^ (k.val * (2 * j.val + 1)) := by
      convert hs using 1
      exact (Fin.sum_congr' (fun j : Fin (2 ^ (n + 1)) => a[j.val] * w ^ (k.val * j.val))
        (pow_succ 2 n).symm).symm
    rw [hs', mul_sum]
    congr 1
    apply sum_congr rfl
    intro j hj
    simp only [Nat.mul_add, Nat.mul_one, pow_add]
    ring

/-- Number of butterfly outputs across the recursion, excluding input preparation. -/
def radixTwoMergeCount : ℕ → ℕ
  | 0 => 0
  | n + 1 => 2 * radixTwoMergeCount n + 2 ^ (n + 1)

/-- Each of the logarithmically many levels has exactly one array length of outputs. -/
theorem radixTwoMergeCount_eq (n : ℕ) : radixTwoMergeCount n = n * 2 ^ n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [radixTwoMergeCount, ih, pow_succ]; ring

end Fourier
