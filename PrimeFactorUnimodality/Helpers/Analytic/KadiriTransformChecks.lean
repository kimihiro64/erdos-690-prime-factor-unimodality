import LeanCert.Validity.DyadicBounds
import PrimeFactorUnimodality.Helpers.Analytic.KadiriR6FourPoints
import PrimeFactorUnimodality.Helpers.Analytic.KadiriTransformExpressions

/-! # One checked scalar row supplies each exact transform bound

The dyadic checker retains every denominator-domain test. Its correctness
theorem and the shared expression semantics supply the actual signed
transform inequality. The four-row assembler uses the existing rational
row family without changing its bounds or its whole-ray consumer.
-/

namespace PrimeFactorUnimodality

open LeanCert.Core LeanCert.Validity

/-- Check one exact rational transform row with explicit precision and Taylor depth. -/
def checkKadiriTransform (θ a₀ a₁ w lower : ℚ) (precision : ℤ) (depth : ℕ) : Bool :=
  checkLowerBoundDyadicChecked (KadiriTransformExpressions.gap θ a₀ a₁ w)
    0 0 (by norm_num) lower precision depth

/-- Successful numerical and domain checks bound the actual signed transform. -/
theorem kadiriTransform_le_of_check (θ a₀ a₁ w lower : ℚ) (precision : ℤ) (depth : ℕ)
    (hprecision : precision ≤ 0)
    (h : checkKadiriTransform θ a₀ a₁ w lower precision depth = true) :
    (lower : ℝ) ≤ kadiriTransformGapClosedForm θ a₀ a₁ w := by
  have hb := verify_lower_bound_dyadic_checked (KadiriTransformExpressions.gap θ a₀ a₁ w)
    0 0 (by norm_num) lower precision depth hprecision h 0 (by norm_num)
  simpa only [KadiriTransformExpressions.gap_eval] using hb

/-- The same checker and scalar configuration are reused for all four requested points. -/
def checkKadiriSixTransformRow (i : Fin 4) (precision : ℤ) (depth : ℕ) : Bool :=
  checkKadiriTransform (185573 / 100000) 1 (1741 / 1000)
    (kadiriSixTransformRow i).1 (kadiriSixTransformRow i).2 precision depth

/-- Checked rows discharge the precise remaining transform premise of the R6 bootstrap. -/
theorem kadiriSixTransformBounds_of_checks (precision : ℤ) (depth : ℕ)
    (hprecision : precision ≤ 0)
    (h : ∀ i : Fin 4, checkKadiriSixTransformRow i precision depth = true) :
    KadiriSixTransformBounds := by
  intro i
  have hb := kadiriTransform_le_of_check (185573 / 100000) 1 (1741 / 1000)
    (kadiriSixTransformRow i).1 (kadiriSixTransformRow i).2 precision depth hprecision (h i)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_one] using hb

end PrimeFactorUnimodality
