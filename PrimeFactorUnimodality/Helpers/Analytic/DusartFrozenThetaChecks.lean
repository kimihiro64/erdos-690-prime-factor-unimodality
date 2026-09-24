import LeanCert.Validity.DyadicBounds
import PrimeFactorUnimodality.Helpers.Analytic.DusartFrozenExpressions

/-! # Checked scalar validity for compact frozen theta rows

One rational geometry check and two checked dyadic bounds imply the existing
row validity predicate. The dyadic checker verifies all inverse, logarithm
and square-root domains as well as the requested upper bounds. Expression
semantics and maximum assembly are shared across every numerical row.
-/

namespace PrimeFactorUnimodality

open LeanCert.Core LeanCert.Validity

namespace DusartFrozenThetaRow

/-- The cheap rational part of row validity, independent of interval evaluation. -/
def checkGeometry (row : DusartFrozenThetaRow) : Bool :=
  decide (25 ≤ row.lower ∧ row.lower ≤ row.upper ∧ row.upper ≤ 5000 ∧
    0 < row.step ∧ (row.orderOffset + 3 : ℕ) * row.step ≤ (1 / 2 : ℚ) ∧
    1 < row.power ∧ row.power < (row.orderOffset + 4 : ℕ))

/-- The same rational checker supplies geometry independently of the chosen scalar bound. -/
theorem geometry_of_checkGeometry {row : DusartFrozenThetaRow}
    (h : row.checkGeometry = true) : row.Geometry := by
  have hg : 25 ≤ row.lower ∧ row.lower ≤ row.upper ∧ row.upper ≤ 5000 ∧
      0 < row.step ∧ (row.orderOffset + 3 : ℕ) * row.step ≤ (1 / 2 : ℚ) ∧
      1 < row.power ∧ row.power < (row.orderOffset + 4 : ℕ) := of_decide_eq_true h
  exact ⟨hg.1, hg.2.1, hg.2.2.1, hg.2.2.2.1, hg.2.2.2.2.1,
    hg.2.2.2.2.2.1, hg.2.2.2.2.2.2⟩

/-- Check both full normalized branches at a specified precision and Taylor depth. -/
def check (row : DusartFrozenThetaRow) (H : ℚ) (precision : ℤ) (depth : ℕ) : Bool :=
  row.checkGeometry &&
    (checkUpperBoundDyadicChecked (DusartFrozenExpressions.moment row H true)
      0 0 (by norm_num) (1 / 5) precision depth &&
    checkUpperBoundDyadicChecked (DusartFrozenExpressions.moment row H false)
      0 0 (by norm_num) (1 / 5) precision depth)

/-- Successful checks establish the exact scalar validity required by the analytic assembler. -/
theorem valid_of_check (row : DusartFrozenThetaRow) (H : ℚ) (precision : ℤ) (depth : ℕ)
    (hprecision : precision ≤ 0) (h : row.check H precision depth = true) : row.Valid H := by
  simp only [check, Bool.and_eq_true] at h
  rcases h with ⟨hg, hl, hr⟩
  have hg' := geometry_of_checkGeometry hg
  have hleft := verify_upper_bound_dyadic_checked (DusartFrozenExpressions.moment row H true)
    0 0 (by norm_num) (1 / 5) precision depth hprecision hl 0 (by norm_num)
  have hright := verify_upper_bound_dyadic_checked (DusartFrozenExpressions.moment row H false)
    0 0 (by norm_num) (1 / 5) precision depth hprecision hr 0 (by norm_num)
  rw [DusartFrozenExpressions.moment_eval _ _ _ _ hg'.lower_ge hg'.step_pos
    hg'.step_small hg'.power_lt] at hleft hright
  norm_num only [Rat.cast_div, Rat.cast_one, Rat.cast_ofNat] at hleft hright
  exact ⟨hg',
    DusartFrozenExpressions.cap_of_branches row H (1 / 5) hleft hright⟩

/-- A family of local checks can be supplied independently of its cheap coverage check. -/
theorem valid_of_checks {rows : List DusartFrozenThetaRow} (H : ℚ)
    (precision : ℤ) (depth : ℕ) (hprecision : precision ≤ 0)
    (hchecks : ∀ row ∈ rows, row.check H precision depth = true) :
    ∀ row ∈ rows, row.Valid H := by
  intro row hrow
  exact row.valid_of_check H precision depth hprecision (hchecks row hrow)

end DusartFrozenThetaRow

end PrimeFactorUnimodality
