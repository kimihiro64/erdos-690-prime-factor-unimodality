import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Real.Basic

set_option autoImplicit false

/-! # List and indexed interval-cover composition

Coverage combinators do not depend on prime counting or analytic prime bounds.
-/

namespace PrimeFactorUnimodality

/-- Closed natural intervals are adjacent when the next left endpoint is
one greater than the preceding right endpoint. -/
def natClosedIntervalChain (left right : Nat) : List (Nat × Nat) → Bool
  | [] => false
  | [row] => (row.1 == left) && (row.2 == right) && decide (row.1 ≤ row.2)
  | row :: next :: rest => (row.1 == left) && decide (row.1 ≤ row.2) &&
      natClosedIntervalChain (row.2 + 1) right (next :: rest)

theorem natClosedIntervalChain_covers
    {rows : List (Nat × Nat)} {left right n : Nat}
    (chain : natClosedIntervalChain left right rows = true)
    (hn : left ≤ n) (hr : n ≤ right) :
    ∃ row ∈ rows, row.1 ≤ n ∧ n ≤ row.2 := by
  induction rows generalizing left with
  | nil => simp [natClosedIntervalChain] at chain
  | cons row rest ih =>
    cases rest with
    | nil =>
      simp only [natClosedIntervalChain, Bool.and_eq_true, beq_iff_eq,
        decide_eq_true_eq] at chain
      exact ⟨row, by simp, by simpa only [chain.1.1] using hn,
        by simpa only [chain.1.2] using hr⟩
    | cons next rest =>
      simp only [natClosedIntervalChain, Bool.and_eq_true, beq_iff_eq,
        decide_eq_true_eq] at chain
      by_cases hrow : n ≤ row.2
      · exact ⟨row, by simp, by simpa only [chain.1.1] using hn, hrow⟩
      · obtain ⟨found, hfound, hleft, hright⟩ := ih chain.2 (by omega)
        exact ⟨found, List.mem_cons_of_mem _ hfound, hleft, hright⟩

theorem indexed_interval_cover_of_list_cover
    {α : Type} (rows : List α) (left right : α → Nat)
    {P Q : Real → Prop}
    (cover : ∀ x : Real, P x → Q x →
      ∃ row ∈ rows, (left row : Real) ≤ x ∧ x ≤ right row) :
    ∀ x : Real, P x → Q x →
      ∃ i : Fin rows.length,
        (left (rows.get i) : Real) ≤ x ∧ x ≤ right (rows.get i) := by
  intro x hP hQ
  obtain ⟨row, hrow, hleft, hright⟩ := cover x hP hQ
  obtain ⟨i, hi, hget⟩ := List.getElem_of_mem hrow
  refine ⟨⟨i, hi⟩, ?_⟩
  simpa [List.get_eq_getElem, hget] using And.intro hleft hright

/-! Indexed tables compose in the same way as list tables.  This is the
compact-block interface used by the finite certificates: a block may be
checked independently, and the kernel only has to check the two coverage
proofs and the numerical junction. -/
theorem indexed_interval_cover_append
    {α : Type} {m X : Real} {n₁ n₂ : Nat}
    (left : Fin n₁ → α) (right : Fin n₂ → α)
    (leftEndpoint rightEndpoint : α → Nat)
    {P Q : Real → Prop}
    (hleft : ∀ x : Real, P x → Q x → x ≤ m →
      ∃ i : Fin n₁,
        (leftEndpoint (left i) : Real) ≤ x ∧
          x ≤ rightEndpoint (left i))
    (hright : ∀ x : Real, P x → Q x → m < x → x ≤ X →
      ∃ i : Fin n₂,
        (leftEndpoint (right i) : Real) ≤ x ∧
          x ≤ rightEndpoint (right i)) :
    ∀ x : Real, P x → Q x → x ≤ X →
      ∃ i : Fin (n₁ + n₂),
        (leftEndpoint (Fin.append left right i) : Real) ≤ x ∧
          x ≤ rightEndpoint (Fin.append left right i) := by
  intro x hP hQ hX
  by_cases hxm : x ≤ m
  · obtain ⟨i, hleft_lower, hleft_upper⟩ := hleft x hP hQ hxm
    refine ⟨Fin.castAdd n₂ i, ?_⟩
    simpa [Fin.append_left] using And.intro hleft_lower hleft_upper
  · obtain ⟨i, hright_lower, hright_upper⟩ :=
      hright x hP hQ (lt_of_not_ge hxm) hX
    refine ⟨Fin.natAdd n₁ i, ?_⟩
    simpa [Fin.append_right] using And.intro hright_lower hright_upper

end PrimeFactorUnimodality
