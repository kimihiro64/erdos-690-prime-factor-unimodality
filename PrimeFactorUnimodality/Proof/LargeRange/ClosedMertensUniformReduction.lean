import PrimeFactorUnimodality.Helpers.Analytic.MertensProvider
import PrimeFactorUnimodality.Proof.LargeRange.UniformAnalyticReduction

set_option autoImplicit false

/-! # Uniform reduction with the proved Mertens input closed -/

namespace PrimeFactorUnimodality

noncomputable section

theorem uniformConstruction_not_isUnimodal_of_closed_mertens
    {qPrev q k bound target : Nat}
    (primeCountingBounds : HasDusartPrimeCountingBounds)
    (consecutive : ConsecutivePrimes qPrev q)
    (qPrev_gt_two : 2 < qPrev) (hk : 4 ≤ k) (bound_pos : 1 ≤ bound)
    (primorial_large : 599 ≤ 9 * primorial q) (target_pos : 1 ≤ target)
    (shellNumeric : (target : Real) < dusartPiLower (9 * primorial q) -
      dusartPiUpper (4 * primorial q))
    (widthNumeric : 5 * primorial q < target * bound)
    (descentDefined : k - 1 ≤ Nat.primeCounting' (2 * primorial q + 1) - 1)
    (prefix_le_primorial : primeAt (k - 2) - 1 ≤ primorial q)
    (descentNumeric : ((k - 1 : Nat) : Real) <
      ((2 * qPrev + 1 : Nat) : Real) *
        (Real.log (Real.log ((primorial q : Nat) : Real)) -
          Real.log (Real.log ((primeAt (k - 2) - 1 : Nat) : Real)) -
          mertensErrorConstant / Real.log ((primorial q : Nat) : Real) -
          mertensErrorConstant / Real.log ((primeAt (k - 2) - 1 : Nat) : Real)))
    (ascentNumeric : (bound : Real) *
      (Real.log (Real.log ((9 * primorial q : Nat) : Real)) + 2 / 3 +
        mertensErrorConstant / Real.log ((9 * primorial q : Nat) : Real) + 1) <
      ((k - 1 : Nat) : Real)) :
    ¬ IsUnimodal (primeFactorDensity k) := by
  apply uniformConstruction_not_isUnimodal_of_mertens_bounds
    primeCountingBounds hasMertensReciprocalPrimeEstimate consecutive
    qPrev_gt_two hk bound_pos primorial_large target_pos shellNumeric
    widthNumeric descentDefined prefix_le_primorial descentNumeric
  have constantBound : Mertens.M ≤ (2 : Real) / 3 :=
    mertensConstant_lt_two_thirds.le
  have boundNonneg : (0 : Real) ≤ (bound : Real) := by positivity
  nlinarith [mul_le_mul_of_nonneg_left constantBound boundNonneg]

theorem uniformConstruction_not_isUnimodal_of_closed_mertens_direct
    {qPrev q k bound : Nat}
    (primeCountingBounds : HasDusartPrimeCountingBounds)
    (consecutive : ConsecutivePrimes qPrev q)
    (qPrev_gt_two : 2 < qPrev) (hk : 4 ≤ k) (bound_pos : 1 ≤ bound)
    (primorial_large : 599 ≤ 9 * primorial q)
    (shellNumeric : ((5 * primorial q : Nat) : Real) / bound + 1 <
      dusartPiLower (9 * primorial q) - dusartPiUpper (4 * primorial q))
    (descentDefined : k - 1 ≤ Nat.primeCounting' (2 * primorial q + 1) - 1)
    (prefix_le_primorial : primeAt (k - 2) - 1 ≤ primorial q)
    (descentNumeric : ((k - 1 : Nat) : Real) <
      ((2 * qPrev + 1 : Nat) : Real) *
        (Real.log (Real.log ((primorial q : Nat) : Real)) -
          Real.log (Real.log ((primeAt (k - 2) - 1 : Nat) : Real)) -
          mertensErrorConstant / Real.log ((primorial q : Nat) : Real) -
          mertensErrorConstant / Real.log ((primeAt (k - 2) - 1 : Nat) : Real)))
    (ascentNumeric : (bound : Real) *
      (Real.log (Real.log ((9 * primorial q : Nat) : Real)) + 2 / 3 +
        mertensErrorConstant / Real.log ((9 * primorial q : Nat) : Real) + 1) <
      ((k - 1 : Nat) : Real)) :
    ¬ IsUnimodal (primeFactorDensity k) := by
  let width : Nat := 5 * primorial q
  let target : Nat := width / bound + 1
  have targetPos : 1 ≤ target := by
    dsimp only [target]
    exact Nat.le_add_left 1 (width / bound)
  have castTargetLe : (target : Real) ≤ (width : Real) / bound + 1 := by
    dsimp only [target]
    push_cast
    have divisionCast : (((width / bound : Nat) : Real)) ≤
        (width : Real) / bound := Nat.cast_div_le
    linarith
  have shellTarget : (target : Real) < dusartPiLower (9 * primorial q) -
      dusartPiUpper (4 * primorial q) :=
    castTargetLe.trans_lt (by simpa only [width] using shellNumeric)
  have widthTarget : width < target * bound := by
    have boundPositive : 0 < bound := by omega
    have remainderLt := Nat.mod_lt width boundPositive
    have decomposition := Nat.mod_add_div width bound
    dsimp only [target]
    calc
      width = width % bound + bound * (width / bound) := decomposition.symm
      _ < bound + bound * (width / bound) :=
        Nat.add_lt_add_right remainderLt _
      _ = (width / bound + 1) * bound := by ring
  apply uniformConstruction_not_isUnimodal_of_closed_mertens
    primeCountingBounds consecutive qPrev_gt_two hk bound_pos primorial_large
    targetPos shellTarget (by simpa only [width] using widthTarget)
    descentDefined prefix_le_primorial descentNumeric ascentNumeric

end

end PrimeFactorUnimodality
