import Mathlib.NumberTheory.Chebyshev

set_option autoImplicit false

namespace PrimeFactorUnimodality

noncomputable section

/-! Compact bounded rows for the direct-computation part of Dusart's Lemma 3.3.

The row validity field is the only place where a bounded numerical proof is
stored.  Coverage and assembly are independent of the eventual row data, so
the finite computation can be split into stable, cacheable chunks. -/
structure DusartLemma33FiniteRow where
  left : Nat
  right : Nat
  left_le_right : left ≤ right
  valid : ∀ x : Real, 0 < x → (left : Real) ≤ x →
    x < (right : Real) + 1 →
      Chebyshev.psi x - Chebyshev.theta x -
          Chebyshev.theta (Real.sqrt x) <
        (1777745 : Real) / 1000000 * x ^ (1 / (3 : Real))

def DusartLemma33FiniteRowsCover
    (rows : List DusartLemma33FiniteRow) (X : Real) : Prop :=
  ∀ x : Real, 0 < x → x ≤ X →
    ∃ row ∈ rows, (row.left : Real) ≤ x ∧
      x < (row.right : Real) + 1

def dusartLemma33FiniteRow_zero_one : DusartLemma33FiniteRow :=
  { left := 0
    right := 1
    left_le_right := by norm_num
    valid := by
      intro x hx _ hright
      have hx2 : x < 2 := by norm_num at hright ⊢; exact hright
      have hsqrt : Real.sqrt x < 2 := by
        nlinarith [Real.sq_sqrt hx.le, Real.sqrt_nonneg x]
      rw [Chebyshev.psi_eq_zero_of_lt_two hx2,
        Chebyshev.theta_eq_zero_of_lt_two hx2,
        Chebyshev.theta_eq_zero_of_lt_two hsqrt]
      norm_num
      positivity }

theorem dusartLemma33FiniteRow_zero_one_cover :
    DusartLemma33FiniteRowsCover [dusartLemma33FiniteRow_zero_one] 1 := by
  intro x hx hX
  refine ⟨dusartLemma33FiniteRow_zero_one, by simp, ?_, ?_⟩
  · simpa [dusartLemma33FiniteRow_zero_one] using hx.le
  · norm_num [dusartLemma33FiniteRow_zero_one]
    linarith

theorem dusart_lemma_3_3_finite_of_rows
    {rows : List DusartLemma33FiniteRow} {X : Real}
    (cover : DusartLemma33FiniteRowsCover rows X) :
    ∀ x : Real, 0 < x → x ≤ X →
      Chebyshev.psi x - Chebyshev.theta x -
          Chebyshev.theta (Real.sqrt x) <
        (1777745 : Real) / 1000000 * x ^ (1 / (3 : Real)) := by
  intro x hx hX
  obtain ⟨row, hrow, hleft, hright⟩ := cover x hx hX
  exact row.valid x hx hleft hright

theorem dusart_lemma_3_3_finite_rows_cover_append
    {left right : List DusartLemma33FiniteRow} {m X : Real}
    (hleft : DusartLemma33FiniteRowsCover left m)
    (hright : DusartLemma33FiniteRowsCover right X) :
    DusartLemma33FiniteRowsCover (left ++ right) X := by
  intro x hx hX
  by_cases hxm : x ≤ m
  · obtain ⟨row, hrow, hleft_row, hright_row⟩ := hleft x hx hxm
    exact ⟨row, by simp [hrow], hleft_row, hright_row⟩
  · obtain ⟨row, hrow, hleft_row, hright_row⟩ :=
      hright x hx hX
    exact ⟨row, by simp [hrow], hleft_row, hright_row⟩

end

end PrimeFactorUnimodality
