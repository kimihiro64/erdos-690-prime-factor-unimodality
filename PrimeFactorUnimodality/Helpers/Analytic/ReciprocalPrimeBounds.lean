import Mathlib.Analysis.SpecialFunctions.Log.Basic
import PrimeFactorUnimodality.Helpers.Analytic.PrimeWeightSum

set_option autoImplicit false

/-! # Interfaces for explicit reciprocal-prime estimates -/

namespace PrimeFactorUnimodality

noncomputable section

/-- An explicit Mertens-style estimate at natural cutoffs.  Keeping the
constant abstract makes the algebraic consequences independent of the
analytic provider used to establish the estimate. -/
def HasReciprocalPrimeEstimate (mertens errorConstant : Real) : Prop :=
  ∀ n : Nat, 2 ≤ n →
    |reciprocalPrimeSumBelow (n + 1) -
      Real.log (Real.log n) - mertens| ≤ errorConstant / Real.log n

/-- The sharper thresholded estimate used in the uniform tail.  Dusart's
published theorem supplies this interface with threshold `2278383` and error
constant `1/5`; the provider remains separate from the algebra below. -/
def HasCubicReciprocalPrimeEstimate
    (mertens errorConstant : Real) (threshold : Nat) : Prop :=
  ∀ n : Nat, threshold ≤ n →
    |reciprocalPrimeSumBelow (n + 1) -
      Real.log (Real.log n) - mertens| ≤
        errorConstant / (Real.log n) ^ 3

/-- The error function in the reciprocal-prime estimate used by
Wang--Crapis.  The rational coefficients are represented exactly. -/
def dusartReciprocalError (x : Real) : Real :=
  1 / (10 * (Real.log x) ^ 2) + 4 / (15 * (Real.log x) ^ 3)

/-- The asymmetric form of Dusart's reciprocal-prime estimate: the lower
bound is valid above one, while the upper bound has the explicit cutoff
`10372`.  Separating the two domains avoids silently strengthening the cited
theorem. -/
def HasDusartReciprocalPrimeEstimate (mertens : Real) : Prop :=
  (∀ n : Nat, 2 ≤ n →
    Real.log (Real.log n) + mertens - dusartReciprocalError n ≤
      reciprocalPrimeSumBelow (n + 1)) ∧
  (∀ n : Nat, 10372 ≤ n →
    reciprocalPrimeSumBelow (n + 1) ≤
      Real.log (Real.log n) + mertens + dusartReciprocalError n)

theorem reciprocalPrimeSumBelow_sub_lower_of_dusart
    {mertens : Real} (estimate : HasDusartReciprocalPrimeEstimate mertens)
    {x y : Nat} (hx : 10372 ≤ x) (hy : 2 ≤ y) :
    Real.log (Real.log y) - Real.log (Real.log x) -
        dusartReciprocalError y - dusartReciprocalError x ≤
      reciprocalPrimeSumBelow (y + 1) - reciprocalPrimeSumBelow (x + 1) := by
  have lower := estimate.1 y hy
  have upper := estimate.2 x hx
  linarith

theorem primeWeightSumBelow_sub_lower_of_dusart
    {mertens : Real} (estimate : HasDusartReciprocalPrimeEstimate mertens)
    {x y : Nat} (hx : 10372 ≤ x) (hy : 2 ≤ y) (hxy : x ≤ y) :
    Real.log (Real.log y) - Real.log (Real.log x) -
        dusartReciprocalError y - dusartReciprocalError x ≤
      primeWeightSumBelow (y + 1) - primeWeightSumBelow (x + 1) := by
  exact (reciprocalPrimeSumBelow_sub_lower_of_dusart estimate hx hy).trans
    (reciprocal_sub_le_primeWeight_sub (Nat.add_le_add_right hxy 1))

theorem primeWeightSumBelow_upper_of_dusart
    {mertens : Real} (estimate : HasDusartReciprocalPrimeEstimate mertens)
    {n : Nat} (hn : 10372 ≤ n) :
    primeWeightSumBelow (n + 1) ≤
      Real.log (Real.log n) + mertens + dusartReciprocalError n + 1 := by
  exact (primeWeightSumBelow_le_reciprocal_add_one (n + 1)).trans
    (by linarith [estimate.2 n hn])

theorem reciprocalPrimeSumBelow_sub_lower_of_cubic_estimate
    {mertens errorConstant : Real} {threshold : Nat}
    (estimate : HasCubicReciprocalPrimeEstimate mertens errorConstant threshold)
    {x y : Nat} (hx : threshold ≤ x) (hy : threshold ≤ y) :
    Real.log (Real.log y) - Real.log (Real.log x) -
        errorConstant / (Real.log y) ^ 3 -
        errorConstant / (Real.log x) ^ 3 ≤
      reciprocalPrimeSumBelow (y + 1) - reciprocalPrimeSumBelow (x + 1) := by
  have lower := (abs_le.mp (estimate y hy)).1
  have upper := (abs_le.mp (estimate x hx)).2
  linarith

theorem reciprocalPrimeSumBelow_sub_upper_of_cubic_estimate
    {mertens errorConstant : Real} {threshold : Nat}
    (estimate : HasCubicReciprocalPrimeEstimate mertens errorConstant threshold)
    {x y : Nat} (hx : threshold ≤ x) (hy : threshold ≤ y) :
    reciprocalPrimeSumBelow (y + 1) - reciprocalPrimeSumBelow (x + 1) ≤
      Real.log (Real.log y) - Real.log (Real.log x) +
        errorConstant / (Real.log y) ^ 3 +
        errorConstant / (Real.log x) ^ 3 := by
  have upper := (abs_le.mp (estimate y hy)).2
  have lower := (abs_le.mp (estimate x hx)).1
  linarith

theorem reciprocalPrimeSumBelow_upper_of_estimate
    {mertens errorConstant : Real}
    (estimate : HasReciprocalPrimeEstimate mertens errorConstant)
    {n : Nat} (hn : 2 ≤ n) :
    reciprocalPrimeSumBelow (n + 1) ≤
      Real.log (Real.log n) + mertens + errorConstant / Real.log n := by
  have h := (abs_le.mp (estimate n hn)).2
  linarith

theorem reciprocalPrimeSumBelow_lower_of_estimate
    {mertens errorConstant : Real}
    (estimate : HasReciprocalPrimeEstimate mertens errorConstant)
    {n : Nat} (hn : 2 ≤ n) :
    Real.log (Real.log n) + mertens - errorConstant / Real.log n ≤
      reciprocalPrimeSumBelow (n + 1) := by
  have h := (abs_le.mp (estimate n hn)).1
  linarith

/-- The unknown Mertens constant cancels when two prime frontiers are
compared. -/
theorem reciprocalPrimeSumBelow_sub_lower_of_estimate
    {mertens errorConstant : Real}
    (estimate : HasReciprocalPrimeEstimate mertens errorConstant)
    {x y : Nat} (hx : 2 ≤ x) (hy : 2 ≤ y) :
    Real.log (Real.log y) - Real.log (Real.log x) -
        errorConstant / Real.log y - errorConstant / Real.log x ≤
      reciprocalPrimeSumBelow (y + 1) - reciprocalPrimeSumBelow (x + 1) := by
  have lower := reciprocalPrimeSumBelow_lower_of_estimate estimate hy
  have upper := reciprocalPrimeSumBelow_upper_of_estimate estimate hx
  linarith

theorem reciprocalPrimeSumBelow_sub_upper_of_estimate
    {mertens errorConstant : Real}
    (estimate : HasReciprocalPrimeEstimate mertens errorConstant)
    {x y : Nat} (hx : 2 ≤ x) (hy : 2 ≤ y) :
    reciprocalPrimeSumBelow (y + 1) - reciprocalPrimeSumBelow (x + 1) ≤
      Real.log (Real.log y) - Real.log (Real.log x) +
        errorConstant / Real.log y + errorConstant / Real.log x := by
  have upper := reciprocalPrimeSumBelow_upper_of_estimate estimate hy
  have lower := reciprocalPrimeSumBelow_lower_of_estimate estimate hx
  linarith

theorem primeWeightSumBelow_upper_of_estimate
    {mertens errorConstant : Real}
    (estimate : HasReciprocalPrimeEstimate mertens errorConstant)
    {n : Nat} (hn : 2 ≤ n) :
    primeWeightSumBelow (n + 1) ≤
      Real.log (Real.log n) + mertens + errorConstant / Real.log n + 1 := by
  exact (primeWeightSumBelow_le_reciprocal_add_one (n + 1)).trans
    (by
      simpa [add_comm] using
        add_le_add_right (reciprocalPrimeSumBelow_upper_of_estimate estimate hn) 1)

theorem primeWeightSumBelow_sub_lower_of_estimate
    {mertens errorConstant : Real}
    (estimate : HasReciprocalPrimeEstimate mertens errorConstant)
    {x y : Nat} (hx : 2 ≤ x) (hy : 2 ≤ y) :
    Real.log (Real.log y) - Real.log (Real.log x) -
        errorConstant / Real.log y - errorConstant / Real.log x - 1 ≤
      primeWeightSumBelow (y + 1) - primeWeightSumBelow (x + 1) := by
  exact (sub_le_sub_right
    (reciprocalPrimeSumBelow_sub_lower_of_estimate estimate hx hy) 1).trans
      (reciprocal_sub_one_le_primeWeight_sub (x + 1) (y + 1))

theorem primeWeightSumBelow_sub_lower_of_estimate_of_le
    {mertens errorConstant : Real}
    (estimate : HasReciprocalPrimeEstimate mertens errorConstant)
    {x y : Nat} (hx : 2 ≤ x) (hy : 2 ≤ y) (hxy : x ≤ y) :
    Real.log (Real.log y) - Real.log (Real.log x) -
        errorConstant / Real.log y - errorConstant / Real.log x ≤
      primeWeightSumBelow (y + 1) - primeWeightSumBelow (x + 1) := by
  exact (reciprocalPrimeSumBelow_sub_lower_of_estimate estimate hx hy).trans
    (reciprocal_sub_le_primeWeight_sub (Nat.add_le_add_right hxy 1))

/-- An upper estimate for a prime-weight shell with the correction term kept
as a decaying telescoping tail instead of the coarse global constant `1`. -/
theorem primeWeightSumBelow_sub_upper_of_estimate
    {mertens errorConstant : Real}
    (estimate : HasReciprocalPrimeEstimate mertens errorConstant)
    {x y : Nat} (hx : 2 ≤ x) (hxy : x ≤ y) :
    primeWeightSumBelow (y + 1) - primeWeightSumBelow (x + 1) ≤
      Real.log (Real.log y) - Real.log (Real.log x) +
        errorConstant / Real.log y + errorConstant / Real.log x +
        (1 / (x : Real) - 1 / (y : Real)) := by
  have reciprocalUpper :=
    reciprocalPrimeSumBelow_sub_upper_of_estimate estimate hx (hx.trans hxy)
  have correctionUpper := primeWeightCorrectionBelow_sub_le_tail
    (x + 1) (y + 1) (by omega) (Nat.add_le_add_right hxy 1)
  rw [primeWeightSumBelow_eq_reciprocal_add_correction,
    primeWeightSumBelow_eq_reciprocal_add_correction]
  norm_num only [Nat.add_sub_cancel] at correctionUpper
  linarith

theorem primeWeightSumBelow_sub_lower_of_cubic_estimate
    {mertens errorConstant : Real} {threshold : Nat}
    (estimate : HasCubicReciprocalPrimeEstimate mertens errorConstant threshold)
    {x y : Nat} (hx : threshold ≤ x) (hy : threshold ≤ y) (hxy : x ≤ y) :
    Real.log (Real.log y) - Real.log (Real.log x) -
        errorConstant / (Real.log y) ^ 3 -
        errorConstant / (Real.log x) ^ 3 ≤
      primeWeightSumBelow (y + 1) - primeWeightSumBelow (x + 1) := by
  exact (reciprocalPrimeSumBelow_sub_lower_of_cubic_estimate
    estimate hx hy).trans
      (reciprocal_sub_le_primeWeight_sub (Nat.add_le_add_right hxy 1))

theorem primeWeightSumBelow_sub_upper_of_cubic_estimate
    {mertens errorConstant : Real} {threshold : Nat}
    (estimate : HasCubicReciprocalPrimeEstimate mertens errorConstant threshold)
    {x y : Nat} (hxTwo : 2 ≤ x) (hx : threshold ≤ x)
    (hy : threshold ≤ y) (hxy : x ≤ y) :
    primeWeightSumBelow (y + 1) - primeWeightSumBelow (x + 1) ≤
      Real.log (Real.log y) - Real.log (Real.log x) +
        errorConstant / (Real.log y) ^ 3 +
        errorConstant / (Real.log x) ^ 3 +
        (1 / (x : Real) - 1 / (y : Real)) := by
  have reciprocalUpper :=
    reciprocalPrimeSumBelow_sub_upper_of_cubic_estimate estimate hx hy
  have correctionUpper := primeWeightCorrectionBelow_sub_le_tail
    (x + 1) (y + 1) (by omega) (Nat.add_le_add_right hxy 1)
  rw [primeWeightSumBelow_eq_reciprocal_add_correction,
    primeWeightSumBelow_eq_reciprocal_add_correction]
  norm_num only [Nat.add_sub_cancel] at correctionUpper
  linarith

end

end PrimeFactorUnimodality
