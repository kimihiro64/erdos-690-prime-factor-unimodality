/-
Copyright (c) 2026 Jonas Whidden.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonas Whidden
-/
import PrimeFactorUnimodality.Mathlib.NumberTheory.PartialSievePrimeLeaves

/-! # Checked external dependency rows for partial-sieve values

An external program supplies values and references, not proof terms. Lean
checks only local integer relations. Strict backward references allow one
induction to certify the entire trace without rerunning the recursive count.
Already verified table leaves can be shared by all later chunks.
-/

namespace PrimeFactorUnimodality

/-- One count claim, indexed by the number of excluded primes and the endpoint. -/
structure PartialSieveClaim where
  level : ℕ
  point : ℕ
  value : ℕ
  deriving DecidableEq

/-- The claim refers to the exact partial-sieve function, not an external count oracle. -/
def PartialSieveClaim.Valid (p : ℕ → ℕ) (row : PartialSieveClaim) : Prop :=
  Nat.sievePhi p row.level row.point = row.value

/-- Prime and coprimality evidence give a checked claim its exact survivor-count meaning. -/
theorem PartialSieveClaim.Valid.coprimeCount {p : ℕ → ℕ} {row : PartialSieveClaim}
    (h : row.Valid p) (hp : ∀ i < row.level, (p i).Prime)
    (hc : ∀ i < row.level, ∀ j < i, Nat.Coprime (p i) (p j)) :
    Nat.coprimeCount (∏ i ∈ Finset.range row.level, p i) row.point = row.value := by
  rw [← Nat.sievePhi_eq p row.level row.point hp hc]
  exact h

/-- A complete prefix past the square-root cutoff turns the checked value into a prime count. -/
theorem PartialSieveClaim.Valid.primeCounting {p : ℕ → ℕ} {row : PartialSieveClaim}
    (h : row.Valid p) (hp : ∀ i < row.level, (p i).Prime)
    (hc : ∀ i < row.level, ∀ j < i, Nat.Coprime (p i) (p j))
    {y : ℕ} (hprod : (∏ i ∈ Finset.range row.level, p i) = primorial y)
    (hn : 1 ≤ row.point) (hy : y ≤ row.point) (hsq : row.point < (y + 1) ^ 2) :
    Nat.primeCounting row.point = row.value + Nat.primeCounting y - 1 := by
  have hv := h.coprimeCount hp hc
  rw [hprod, Nat.coprimeCount_primorial_eq hn hy hsq] at hv
  have := Nat.monotone_primeCounting hy
  omega

/-- Three local reasons cover unsieved intervals, retained leaves, and recurrence steps. -/
inductive PartialSieveReason where
  | initial
  | known (index : ℕ)
  | split (left right : ℕ)

/-- A data row stores each result once and points to previously verified dependencies. -/
structure PartialSieveRow where
  claim : PartialSieveClaim
  reason : PartialSieveReason

/-- Local checks include every endpoint, level, dependency bound, and arithmetic relation. -/
def checkPartialSieveRow (p : ℕ → ℕ) (known : ℕ → PartialSieveClaim) (knownSize : ℕ)
    (rows : ℕ → PartialSieveRow) (i : ℕ) : Bool :=
  let r := (rows i).claim
  match (rows i).reason with
  | .initial => decide (r.level = 0 ∧ r.value = r.point)
  | .known k => decide (k < knownSize ∧ known k = r)
  | .split l h =>
    let left := (rows l).claim
    let right := (rows h).claim
    decide (l < i ∧ h < i ∧ 0 < r.level ∧
      left.level + 1 = r.level ∧ right.level = left.level ∧
      left.point = r.point ∧ right.point = r.point / p left.level ∧
      r.value + right.value = left.value)

/-- Local checks and certified leaves prove all rows, even when subcomputations are shared. -/
theorem partialSieveRows_valid (p : ℕ → ℕ) {known : ℕ → PartialSieveClaim}
    {knownSize : ℕ} (hknown : ∀ k < knownSize, (known k).Valid p)
    {rows : ℕ → PartialSieveRow} {size : ℕ}
    (hcheck : ∀ i < size, checkPartialSieveRow p known knownSize rows i = true) :
    ∀ i < size, (rows i).claim.Valid p := by
  intro i hi
  induction i using Nat.strong_induction_on with
  | h i ih =>
    have hc := hcheck i hi
    unfold checkPartialSieveRow at hc
    cases he : (rows i).reason with
    | initial =>
      simp only [he, decide_eq_true_eq] at hc
      simp only [PartialSieveClaim.Valid, hc.1, Nat.sievePhi]
      exact hc.2.symm
    | known k =>
      simp only [he, decide_eq_true_eq] at hc
      exact hc.2 ▸ hknown k hc.1
    | split l r =>
      simp only [he, decide_eq_true_eq] at hc
      obtain ⟨hl, hr, ha, hla, hra, hln, hrn, hv⟩ := hc
      have hleft := ih l hl (by omega)
      have hright := ih r hr (by omega)
      unfold PartialSieveClaim.Valid at hleft hright ⊢
      rw [← hla, Nat.sievePhi, ← hln, hleft]
      rw [hra, hrn, ← hln] at hright
      rw [hright]
      omega

/-- Any disjoint range of checked indices can be validated independently and then joined. -/
theorem checkPartialSieveRows_join {p : ℕ → ℕ} {known : ℕ → PartialSieveClaim}
    {knownSize : ℕ} {rows : ℕ → PartialSieveRow} {a b : ℕ}
    (ha : ∀ i < a, checkPartialSieveRow p known knownSize rows i = true)
    (hb : ∀ i, a ≤ i → i < b → checkPartialSieveRow p known knownSize rows i = true) :
    ∀ i < b, checkPartialSieveRow p known knownSize rows i = true := by
  intro i hi
  by_cases h : i < a
  · exact ha i h
  · exact hb i (by omega) hi

end PrimeFactorUnimodality
