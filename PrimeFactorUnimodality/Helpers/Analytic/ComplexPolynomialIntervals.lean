import PrimeFactorUnimodality.Helpers.Analytic.ComplexInterval
import PrimeFactorUnimodality.Mathlib.Algebra.BigOperators.Ring.Horner

/-! # Linear-pass complex polynomial enclosures

Horner evaluation reuses each partial polynomial, avoiding independently
computed powers. The exact finite-sum identity covers every coefficient
in a consecutive slice, including an empty or shifted slice.
-/

namespace PrimeFactorUnimodality.ComplexInterval

open Complex Finset

/-- A complex interval Horner fold, multiplying the shared tail on the right. -/
def horner (X : ComplexInterval) : List ComplexInterval → ComplexInterval
  | [] => point ⟨0, 0⟩
  | a :: rest => a.add ((horner X rest).mul X)

/-- Coefficientwise enclosure and one input enclosure imply the entire Horner enclosure. -/
theorem mem_horner {x : ℂ} {X : ComplexInterval} (hx : x ∈ X)
    {values : List ℂ} {coefficients : List ComplexInterval}
    (h : List.Forall₂ (fun z J => z ∈ J) values coefficients) :
    values.foldr (fun a b => a + b * x) 0 ∈ horner X coefficients := by
  induction h with
  | nil => simpa [horner] using mem_constant 0
  | cons hw ht ih => exact mem_add hw (mem_mul ih hx)

/-- Materialize a short consecutive coefficient slice and evaluate it once. -/
def polynomial (X : ComplexInterval) (coefficient : ℕ → ComplexInterval)
    (start count : ℕ) : ComplexInterval :=
  horner X ((List.range' start count).map coefficient)

/-- The interval result encloses the exact finite power sum, with no missing coefficients. -/
theorem mem_polynomial {x : ℂ} {X : ComplexInterval} (hx : x ∈ X)
    (weight : ℕ → ℂ) (coefficient : ℕ → ComplexInterval) (start count : ℕ)
    (h : ∀ n ∈ List.range' start count, weight n ∈ coefficient n) :
    (∑ j ∈ range count, weight (start + j) * x ^ j) ∈
      polynomial X coefficient start count := by
  rw [← List.foldr_horner_range']
  apply mem_horner hx
  have hlist (l : List ℕ) (hl : ∀ n ∈ l, weight n ∈ coefficient n) :
      List.Forall₂ (fun z J => z ∈ J) (l.map weight) (l.map coefficient) := by
    induction l with
    | nil => exact .nil
    | cons n rest ih =>
      exact .cons (hl n (by simp)) (ih (fun k hk => hl k (by simp [hk])))
  exact hlist _ h

end PrimeFactorUnimodality.ComplexInterval
