import PrimeFactorUnimodality.Helpers.Analytic.MomentBlockPartition

/-! # Shared-moment interfaces and small rational regression cases -/

set_option autoImplicit false

namespace PrimeFactorUnimodality.Tests

noncomputable section

open Complex Finset LeanCert.Core
open PrimeFactorUnimodality.DirichletMomentBlock

variable {degree : ℕ}

example (lo hi : ℕ) (rows : List (DirichletMomentBlock degree)) :
    checkChain lo hi rows = true ↔ Chain lo hi rows := by
  exact PrimeFactorUnimodality.DirichletMomentBlock.checkChain_eq_true lo hi rows

example {rows : List (DirichletMomentBlock degree)}
    (h : checkGroups rows = true) : (rows.map group).Nodup := by
  exact PrimeFactorUnimodality.DirichletMomentBlock.nodup_of_checkGroups h

example (lo hi : ℕ) (rows : List (DirichletMomentBlock degree))
    (h : checkPartition lo hi rows = true) :
    Chain lo hi rows ∧ (rows.map group).Nodup := by
  exact PrimeFactorUnimodality.DirichletMomentBlock.checkPartition_sound lo hi rows h

example {lo mid hi : ℕ} {left right : List (DirichletMomentBlock degree)}
    (hl : Chain lo mid left) (hr : Chain mid hi right) : Chain lo hi (left ++ right) := by
  exact PrimeFactorUnimodality.DirichletMomentBlock.Chain.append hl hr

example {lo hi : ℕ} {rows : List (DirichletMomentBlock degree)}
    (h : Chain lo hi rows) : lo ≤ hi := by
  exact PrimeFactorUnimodality.DirichletMomentBlock.Chain.ordered h

example {lo hi : ℕ} {rows : List (DirichletMomentBlock degree)}
    (h : Chain lo hi rows) {r : DirichletMomentBlock degree} (hr : r ∈ rows) :
    lo ≤ r.first ∧ r.stop ≤ hi := by
  exact PrimeFactorUnimodality.DirichletMomentBlock.Chain.bounds h hr

example {lo hi : ℕ} {rows : List (DirichletMomentBlock degree)}
    (h : Chain lo hi rows) {n : ℕ} (hn : lo ≤ n ∧ n < hi) :
    ∃ r ∈ rows, n ∈ Ico r.first r.stop ∧ binAt rows n = r.group := by
  exact PrimeFactorUnimodality.DirichletMomentBlock.Chain.select h hn

example {lo hi : ℕ} {rows : List (DirichletMomentBlock degree)}
    (h : Chain lo hi rows) {r : DirichletMomentBlock degree} (hr : r ∈ rows)
    {n : ℕ} (hn : n ∈ Ico r.first r.stop) : binAt rows n = r.group := by
  exact PrimeFactorUnimodality.DirichletMomentBlock.Chain.binAt_eq h hr hn

example {lo hi : ℕ} {rows : List (DirichletMomentBlock degree)}
    (h : Chain lo hi rows) (hlabels : (rows.map group).Nodup)
    {r : DirichletMomentBlock degree} (hr : r ∈ rows) :
    ((Ico lo hi).filter (fun n => binAt rows n = r.group)) = Ico r.first r.stop := by
  exact PrimeFactorUnimodality.DirichletMomentBlock.Chain.filter_eq h hlabels hr

def leftBlock : DirichletMomentBlock 0 := ⟨1, 3, 0, #v[], #v[]⟩
def rightBlock : DirichletMomentBlock 0 := ⟨3, 5, -1, #v[], #v[]⟩
example : checkChain 1 5 [leftBlock, rightBlock] = true := by decide +kernel
example : checkChain 1 5 [leftBlock, {rightBlock with first := 4}] = false := by decide +kernel
example : checkChain 1 5 ([] : List (DirichletMomentBlock 0)) = false := by decide +kernel
example : checkChain 5 5 ([] : List (DirichletMomentBlock 0)) = true := by decide +kernel
example : binAt [leftBlock, rightBlock] 3 = -1 := by decide +kernel
example : checkPartition 1 5 [leftBlock, rightBlock] = true := by decide +kernel
example : checkPartition 1 5 [leftBlock, {rightBlock with group := 0}] = false := by decide +kernel
example : checkPartition 1 5 [leftBlock, {rightBlock with group := 1}] = false := by decide +kernel

end

end PrimeFactorUnimodality.Tests
