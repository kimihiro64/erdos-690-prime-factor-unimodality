import PrimeFactorUnimodality.Helpers.Analytic.DusartFrozenThetaChecks
import PrimeFactorUnimodality.Helpers.Analytic.DusartReflectedExpressions

/-! # Shared checked validity for reflected scalar rows

Positive height, the existing geometry checker, and two domain-checked
dyadic upper bounds imply reflected validity. Coverage remains independent
and uses the same row list and exact endpoint checker as the original path.
-/

namespace PrimeFactorUnimodality

open LeanCert.Core LeanCert.Validity

namespace DusartFrozenThetaRow

/-- Check both reflected branches without suppressing inverse or logarithm domain checks. -/
def checkReflected (row : DusartFrozenThetaRow) (H : ℚ) (precision : ℤ) (depth : ℕ) : Bool :=
  decide (0 < H) && (row.checkGeometry &&
    (checkUpperBoundDyadicChecked (DusartReflectedExpressions.moment row H true)
      0 0 (by norm_num) (1 / 5) precision depth &&
    checkUpperBoundDyadicChecked (DusartReflectedExpressions.moment row H false)
      0 0 (by norm_num) (1 / 5) precision depth))

/-- Every successful reflected check supplies the exact cap in the analytic row theorem. -/
theorem reflectedValid_of_check (row : DusartFrozenThetaRow) (H : ℚ) (precision : ℤ) (depth : ℕ)
    (hprecision : precision ≤ 0) (h : row.checkReflected H precision depth = true) :
    row.ReflectedValid H := by
  simp only [checkReflected, Bool.and_eq_true] at h
  rcases h with ⟨hH, hg, hl, hr⟩
  have hH' : 0 < H := of_decide_eq_true hH
  have hg' := geometry_of_checkGeometry hg
  have hleft := verify_upper_bound_dyadic_checked (DusartReflectedExpressions.moment row H true)
    0 0 (by norm_num) (1 / 5) precision depth hprecision hl 0 (by norm_num)
  have hright := verify_upper_bound_dyadic_checked (DusartReflectedExpressions.moment row H false)
    0 0 (by norm_num) (1 / 5) precision depth hprecision hr 0 (by norm_num)
  rw [DusartReflectedExpressions.moment_eval _ _ _ _ hg' hH'] at hleft hright
  norm_num only [Rat.cast_div, Rat.cast_one, Rat.cast_ofNat] at hleft hright
  exact ⟨hg', DusartReflectedExpressions.cap_of_branches row H (1 / 5) hleft hright⟩

/-- Independently checked reflected rows supply a membership-based validity family. -/
theorem reflectedValid_of_checks {rows : List DusartFrozenThetaRow} (H : ℚ)
    (precision : ℤ) (depth : ℕ) (hprecision : precision ≤ 0)
    (hchecks : ∀ row ∈ rows, row.checkReflected H precision depth = true) :
    ∀ row ∈ rows, row.ReflectedValid H := by
  intro row hrow
  exact row.reflectedValid_of_check H precision depth hprecision (hchecks row hrow)

end DusartFrozenThetaRow

end PrimeFactorUnimodality
