import PrimeFactorUnimodality.Helpers.Analytic.PrimeCountingReciprocalShell
import PrimeFactorUnimodality.Proof.LargeRange.ClosedMertensTailBounds
import PrimeFactorUnimodality.Proof.LargeRange.TailErrorBounds
import PrimeFactorUnimodality.Proof.LargeRange.TailPrimeCountingBounds
import PrimeFactorUnimodality.Proof.LargeRange.TailShellNumerics
import PrimeFactorUnimodality.Proof.LargeRange.UniformValley

set_option autoImplicit false

/-! # Uniform CRT tail from the finite prime-counting shell

Finite Abel summation supplies the descent. The proved Mertens upper estimate
supplies the ascent. This closes the reciprocal-prime input from `38001`
without the full published record-gap certificate or a sharp Mertens error.
-/

namespace PrimeFactorUnimodality

noncomputable section

theorem uniformTail_not_isUnimodal_of_tailTheta
    (primeCountingBounds : HasDusartPrimeCountingBounds)
    (thetaBounds : HasTailThetaBounds)
    (tailPair : HasUniformTailPrimePair)
    {k : Nat} (hk : 38001 ≤ k) :
    ¬ IsUnimodal (primeFactorDensity k) := by
  let r := k - 1
  have hr : 38000 ≤ r := by dsimp only [r]; omega
  obtain ⟨qPrev, q, consecutive, prevLarge, scaleLtQ, qUpper, scalePrev⟩ :=
    tailPair r hr
  apply uniformConstruction_not_isUnimodal_of_weight_bounds_direct
    primeCountingBounds consecutive
  · exact tail_predecessor_gt_two (by omega : 3301 ≤ qPrev)
  · omega
  · exact tailGapBound_pos q
  · exact tail_primorial_large hr scaleLtQ
  · exact tail_primeCounting_shell_numeric thetaBounds hr scaleLtQ qUpper
  · simpa only [r, Nat.sub_add_cancel (show 1 ≤ k by omega)] using
      tail_descentDefined primeCountingBounds thetaBounds hr scaleLtQ
  · have prefixLarge : 600 ≤ primeAt (k - 2) - 1 := by
      have h := tail_ten_mul_le_prefix primeCountingBounds hr
      dsimp only [r] at h
      rw [show k - 1 - 1 = k - 2 by omega] at h
      omega
    have prefixLe : primeAt (k - 2) - 1 ≤ primorial q := by
      have h := tail_prefix_le_primorial primeCountingBounds thetaBounds hr scaleLtQ
      simpa only [r, show k - 1 - 1 = k - 2 by omega] using h
    have shell := primeWeightSumBelow_sub_lower_of_primeCounting
      primeCountingBounds prefixLarge prefixLe
    have cutoff : primeAt (k - 2) - 1 + 1 = primeAt (k - 2) := by
      have h := one_lt_primeAt (k - 2)
      omega
    rw [cutoff] at shell
    have descent := tail_descent_numeric_of_primeCounting
      thetaBounds primeCountingBounds hr scaleLtQ scalePrev
    have scaled := mul_le_mul_of_nonneg_left shell
      (show (0 : Real) ≤ ((2 * qPrev + 1 : Nat) : Real) by positivity)
    apply lt_of_lt_of_le ?_ scaled
    simpa only [r, show k - 1 - 1 = k - 2 by omega] using descent
  · have ascent := tail_ascent_numeric_closed_mertens
      thetaBounds hr scaleLtQ qUpper
    have sumUpper := primeWeightSumBelow_upper_of_estimate
      hasMertensReciprocalPrimeEstimate (show 2 ≤ 9 * primorial q by
        have h := primorial_pos q
        omega)
    have constantUpper := mertensConstant_lt_two_thirds.le
    have upper : primeWeightSumBelow (9 * primorial q + 1) ≤
        Real.log (Real.log ((9 * primorial q : Nat) : Real)) + 2 / 3 +
          mertensErrorConstant / Real.log ((9 * primorial q : Nat) : Real) + 1 := by
      linarith
    exact (mul_le_mul_of_nonneg_left upper
      (show (0 : Real) ≤ (tailGapBound q : Real) by positivity)).trans_lt
        (by simpa only [r] using ascent)

/-- The original Dusart boundary is preserved as an adapter to the weaker
theta requirements of the same uniform construction. -/
theorem uniformTail_not_isUnimodal_closed_mertens
    (primeCountingBounds : HasDusartPrimeCountingBounds)
    (thetaBounds : HasDusartThetaBounds)
    (tailPair : HasUniformTailPrimePair)
    {k : Nat} (hk : 38001 ≤ k) :
    ¬ IsUnimodal (primeFactorDensity k) :=
  uniformTail_not_isUnimodal_of_tailTheta primeCountingBounds
    (hasTailThetaBounds_of_dusart thetaBounds) tailPair hk

end

end PrimeFactorUnimodality
