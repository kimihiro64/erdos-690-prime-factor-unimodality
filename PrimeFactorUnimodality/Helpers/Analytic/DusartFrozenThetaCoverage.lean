import PrimeFactorUnimodality.Helpers.Analytic.DusartFrozenThetaRows

/-! # Ordered coverage and assembly for frozen theta rows

Rational endpoint checks establish continuous coverage independently of
the expensive scalar checks. Chunks append through one shared endpoint.
The assembler uses membership to reuse each row's analytic theorem; no
scalar computation is repeated for individual interior points.
-/

namespace PrimeFactorUnimodality

namespace DusartFrozenThetaRow

/-- A nonempty chain of ordered intervals with exactly shared endpoints. -/
inductive Covers : ℚ → ℚ → List DusartFrozenThetaRow → Prop
  | single (row : DusartFrozenThetaRow) (h : row.lower ≤ row.upper) :
      Covers row.lower row.upper [row]
  | cons (row : DusartFrozenThetaRow) {last : ℚ} {tail : List DusartFrozenThetaRow}
      (h : row.lower ≤ row.upper) (rest : Covers row.upper last tail) :
      Covers row.lower last (row :: tail)

/-- Independently certified chunks compose without repeating a row at the seam. -/
theorem Covers.append {a b c : ℚ} {left right : List DusartFrozenThetaRow}
    (hl : Covers a b left) (hr : Covers b c right) : Covers a c (left ++ right) := by
  induction hl with
  | single row h => exact Covers.cons row h hr
  | cons row h _ ih => exact Covers.cons row h (ih hr)

/-- The endpoint checker rejects empty coverage and requires exact adjacency. -/
def checkCoverage (first last : ℚ) : List DusartFrozenThetaRow → Bool
  | [] => false
  | row :: tail => decide (first = row.lower ∧ row.lower ≤ row.upper) &&
      match tail with
      | [] => decide (row.upper = last)
      | _ :: _ => checkCoverage row.upper last tail

/-- Boolean coverage checks construct the ordered chain used by the analytic proof. -/
theorem covers_of_checkCoverage {first last : ℚ} {rows : List DusartFrozenThetaRow}
    (h : checkCoverage first last rows = true) : Covers first last rows := by
  induction rows generalizing first with
  | nil => simp [checkCoverage] at h
  | cons row tail ih =>
    cases tail with
    | nil =>
      simp only [checkCoverage, Bool.and_eq_true, decide_eq_true_eq] at h
      rcases h with ⟨⟨rfl, hord⟩, rfl⟩
      exact Covers.single row hord
    | cons next rest =>
      change (decide (first = row.lower ∧ row.lower ≤ row.upper) &&
        checkCoverage row.upper last (next :: rest)) = true at h
      rw [Bool.and_eq_true, decide_eq_true_eq] at h
      rcases h with ⟨⟨rfl, hord⟩, htail⟩
      exact Covers.cons row hord (ih htail)

/-- Coverage is over all real logarithms, including every shared endpoint. -/
theorem Covers.covers {a b : ℚ} {rows : List DusartFrozenThetaRow}
    (h : Covers a b rows) {y : ℝ} (hlo : (a : ℝ) ≤ y) (hhi : y ≤ b) :
    ∃ row ∈ rows, (row.lower : ℝ) ≤ y ∧ y ≤ row.upper := by
  induction h with
  | single row _ => exact ⟨row, by simp, hlo, hhi⟩
  | cons row _ _ ih =>
    by_cases hy : y ≤ row.upper
    · exact ⟨row, by simp, hlo, hy⟩
    · obtain ⟨next, hmem, hnext⟩ := ih (le_of_not_ge hy) hhi
      exact ⟨next, List.mem_cons_of_mem row hmem, hnext⟩

/-- Scalar validity is compositional independently of endpoint coverage. -/
theorem valid_append {H : ℝ} {left right : List DusartFrozenThetaRow}
    (hl : ∀ row ∈ left, row.Valid H) (hr : ∀ row ∈ right, row.Valid H) :
    ∀ row ∈ left ++ right, row.Valid H := by
  intro row hrow
  rcases List.mem_append.mp hrow with h | h
  · exact hl row h
  · exact hr row h

/-- Valid covering rows give the exact theta coefficient throughout the complete real band. -/
theorem Covers.bound {a b : ℚ} {rows : List DusartFrozenThetaRow} {H x : ℝ}
    (h : Covers a b rows) (hvalid : ∀ row ∈ rows, row.Valid H)
    (hH : 25000000 ≤ H) (hH₁ : H ≤ 1000000000)
    (hlow : ∀ z ∈ xiLowHeightIndices H,
      (riemannXiDivisorZeroValue z).re ≤ (1 / 2 : ℝ))
    (hreg : ∀ z : RiemannXiDivisorZeroIndex, H ≤ |(riemannXiDivisorZeroValue z).im| →
      (riemannXiDivisorZeroValue z).re ≤
        1 - 1 / (6 * Real.log |(riemannXiDivisorZeroValue z).im|))
    (hx : 0 < x) (hlo : (a : ℝ) ≤ Real.log x) (hhi : Real.log x ≤ b) :
    |Chebyshev.theta x - x| ≤ (1 / 5 : ℝ) * x / Real.log x ^ 2 := by
  obtain ⟨row, hrow, hleft, hright⟩ := h.covers hlo hhi
  exact (hvalid row hrow).bound hH hH₁ hlow hreg hx hleft hright

end DusartFrozenThetaRow

end PrimeFactorUnimodality
