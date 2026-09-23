/-
Copyright (c) 2026 Jonas Whidden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonas Whidden
-/
import PrimeFactorUnimodality.Mathlib.Analysis.Complex.RationalPoint
import PrimeFactorUnimodality.Mathlib.Analysis.Fourier.RadixError
import PrimeFactorUnimodality.Mathlib.Analysis.Fourier.RadixRoot

/-! # Executable rational checks for shared radix computations

Arithmetic validation uses only rational operations and Boolean array
folds. Twiddles are shared by depth across all nodes and transform columns;
their analytic enclosure is supplied once to the soundness theorem.
-/

namespace Fourier

open Complex

/-- A shared Boolean traversal of every index, without an emitted proof per index. -/
def allIndices {N : ℕ} (f : Fin N → Bool) : Bool := (Vector.ofFn f).all id

/-- The traversal checks the entire typed index domain. -/
theorem allIndices_eq_true {N : ℕ} (f : Fin N → Bool) :
    allIndices f = true ↔ ∀ k, f k = true := by
  simp only [allIndices, Vector.all_eq_true, Vector.getElem_ofFn, id_eq]
  constructor
  · intro h k; exact h k.val k.isLt
  · intro h i hi; exact h ⟨i, hi⟩

/-- One rational twiddle table and uniform error per positive depth. -/
structure RationalTwiddles where
  table : (n : ℕ) → Vector RationalPoint (2 ^ (n + 1))
  error : ℕ → ℚ

/-- Each required table encloses its canonical exact phases. -/
def RationalTwiddles.Valid (p : RationalTwiddles) (depth : ℕ) : Prop :=
  ∀ n < depth, 0 ≤ (p.error n : ℝ) ∧ ∀ k : Fin (2 ^ (n + 1)),
    ‖radixRoot (n + 1) ^ k.val - (p.table n)[k.val].toComplex‖ ≤ (p.error n : ℝ)

/-- Shared twiddle validity restricts to a shorter transform. -/
theorem RationalTwiddles.Valid.mono {p : RationalTwiddles} {n m : ℕ}
    (hp : p.Valid n) (hm : m ≤ n) : p.Valid m :=
  fun j hj => hp j (lt_of_lt_of_le hj hm)

/-- Only rational output arrays and arithmetic budgets are stored at each node. -/
inductive RationalTrace : ℕ → Type
  | leaf (value : RationalPoint) (error : ℚ) : RationalTrace 0
  | node {n : ℕ} (even odd : RationalTrace n) (output : Vector RationalPoint (2 ^ (n + 1)))
      (rounding rightCap : ℚ) : RationalTrace (n + 1)

/-- The current rational output array, shared with its parent. -/
def RationalTrace.values : {n : ℕ} → RationalTrace n → Vector RationalPoint (2 ^ n)
  | 0, .leaf value _ => Vector.singleton value
  | _ + 1, .node _ _ output _ _ => output

/-- Interpret one rational trace using the common depth-indexed twiddle tables. -/
def RationalTrace.semantic (p : RationalTwiddles) : {n : ℕ} → RationalTrace n → RadixTrace n
  | 0, .leaf value error => .leaf value.toComplex error
  | n + 1, .node l r out ε M => .node (l.semantic p) (r.semantic p)
      (out.map RationalPoint.toComplex) ((p.table n).map RationalPoint.toComplex)
      ε (p.error n) M

/-- Interpretation preserves the output array entrywise. -/
@[simp] theorem RationalTrace.values_semantic (p : RationalTwiddles) {n : ℕ}
    (t : RationalTrace n) : (t.semantic p).values = t.values.map RationalPoint.toComplex := by
  cases t <;> simp [RationalTrace.semantic, RadixTrace.values, RationalTrace.values]

/-- Complete rational error budget, retaining both children, twiddle and rounding errors. -/
def RationalTrace.error (p : RationalTwiddles) : {n : ℕ} → RationalTrace n → ℚ
  | 0, .leaf _ error => error
  | n + 1, .node l r _ rounding cap => l.error p + r.error p + cap * p.error n + rounding

/-- The computable budget is exactly the error of the interpreted complex trace. -/
@[simp] theorem RationalTrace.error_semantic (p : RationalTwiddles) {n : ℕ} (t : RationalTrace n) :
    (t.semantic p).error = (t.error p : ℝ) := by
  induction t with
  | leaf => rfl
  | node l r out e cap ihl ihr =>
    simp [RationalTrace.semantic, RadixTrace.error, RationalTrace.error, ihl, ihr]

/-- Every leaf and arithmetic merge is checked with exact rational squared norms. -/
def RationalTrace.check (p : RationalTwiddles) : {n : ℕ} → RationalTrace n →
    Vector RationalPoint (2 ^ n) → Bool
  | 0, .leaf value error, a => (a[0].sub value).normLE error
  | n + 1, .node l r out ε M, a =>
    l.check p (evenSamples n a) && r.check p (oddSamples n a) &&
    allIndices (fun k : Fin (2 ^ n) => r.values[k.val].normLE M) &&
    allIndices (fun k : Fin (2 ^ (n + 1)) =>
      let j : Fin (2 ^ n) := ⟨k.val % (2 ^ n), Nat.mod_lt _ (by positivity)⟩
      ((l.values[j.val].add ((p.table n)[k.val].mul r.values[j.val])).sub out[k.val]).normLE ε)

/-- Taking the even half commutes with entrywise interpretation. -/
theorem evenSamples_map {α β : Type*} (n : ℕ) (f : α → β) (a : Vector α (2 ^ (n + 1))) :
    evenSamples n (a.map f) = (evenSamples n a).map f := by
  apply Vector.ext
  intro i hi
  simp [evenSamples]

/-- Taking the odd half commutes with entrywise interpretation. -/
theorem oddSamples_map {α β : Type*} (n : ℕ) (f : α → β) (a : Vector α (2 ^ (n + 1))) :
    oddSamples n (a.map f) = (oddSamples n a).map f := by
  apply Vector.ext
  intro i hi
  simp [oddSamples]

/-- The executable checker discharges the complete semantic trace obligation. -/
theorem RationalTrace.valid_of_check {p : RationalTwiddles} {n : ℕ} (hp : p.Valid n)
    (t : RationalTrace n) (a : Vector RationalPoint (2 ^ n)) (h : t.check p a = true) :
    (t.semantic p).Valid (radixRoot n) (a.map RationalPoint.toComplex) := by
  induction t with
  | leaf value error =>
    simpa only [RationalTrace.semantic, RadixTrace.Valid, Vector.getElem_map,
      RationalPoint.toComplex_sub] using (RationalPoint.normLE_eq_true _ _).mp h
  | @node n l r out ε M ihl ihr =>
    simp only [RationalTrace.check, Bool.and_eq_true, allIndices_eq_true] at h
    rcases h with ⟨⟨⟨hl, hr⟩, hcap⟩, hmerge⟩
    have hp' := hp.mono (Nat.le_succ n)
    refine ⟨?_, ?_, (hp n (Nat.lt_succ_self n)).1, ?_, ?_, ?_⟩
    · rw [radixRoot_succ_sq, evenSamples_map]
      exact ihl hp' _ hl
    · rw [radixRoot_succ_sq, oddSamples_map]
      exact ihr hp' _ hr
    · intro k
      simpa only [Vector.getElem_map] using (hp n (Nat.lt_succ_self n)).2 k
    · intro k
      simpa only [RationalTrace.values_semantic, Vector.getElem_map] using
        (RationalPoint.normLE_eq_true _ _).mp (hcap k)
    · intro k
      simpa only [RationalTrace.values_semantic, Vector.getElem_map,
        RationalPoint.toComplex_sub, RationalPoint.toComplex_add, RationalPoint.toComplex_mul] using
          (RationalPoint.normLE_eq_true _ _).mp (hmerge k)

end Fourier
