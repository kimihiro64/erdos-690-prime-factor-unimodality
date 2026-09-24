import PrimeFactorUnimodality.Proof.LargeRange.TailAscentBounds
import PrimeFactorUnimodality.Proof.LargeRange.TailErrorBounds
import PrimeFactorUnimodality.Proof.LargeRange.TailPrimeCountingBounds
import PrimeFactorUnimodality.Proof.LargeRange.UniformAnalyticReduction

set_option autoImplicit false

/-! # Closed numerical assembly of the uniform tail -/

namespace PrimeFactorUnimodality

noncomputable section

theorem uniformTail_not_isUnimodal
    {mertens : Real}
    (primeCountingBounds : HasDusartPrimeCountingBounds)
    (reciprocalEstimate : HasDusartReciprocalPrimeEstimate mertens)
    (mertens_le : mertens ≤ (2 : Real) / 3)
    (thetaBounds : HasDusartThetaBounds)
    (tailPair : HasUniformTailPrimePair)
    {k : Nat} (hk : 38001 ≤ k) :
    ¬ IsUnimodal (primeFactorDensity k) := by
  have thetaBounds := hasTailThetaBounds_of_dusart thetaBounds
  let r := k - 1
  have hr : 38000 ≤ r := by dsimp only [r]; omega
  obtain ⟨qPrev, q, consecutive, prevLarge, scaleLtQ, qUpper, scalePrev⟩ :=
    tailPair r hr
  apply uniformConstruction_not_isUnimodal_of_dusart_reciprocal_direct
    primeCountingBounds reciprocalEstimate consecutive
  · exact tail_predecessor_gt_two (by omega : 3301 ≤ qPrev)
  · omega
  · exact tailGapBound_pos q
  · exact tail_primorial_large hr scaleLtQ
  · exact tail_ascentThreshold hr scaleLtQ
  · exact tail_primeCounting_shell_numeric thetaBounds hr scaleLtQ qUpper
  · simpa only [r, Nat.sub_add_cancel (show 1 ≤ k by omega)] using
      tail_descentDefined primeCountingBounds thetaBounds hr scaleLtQ
  · exact tail_prefixThreshold (by omega)
  · have hprefix := tail_prefix_le_primorial
      primeCountingBounds thetaBounds hr scaleLtQ
    simpa only [r, show k - 1 - 1 = k - 2 by omega] using hprefix
  · have descent := tail_descent_numeric thetaBounds primeCountingBounds
      hr scaleLtQ scalePrev
    simpa only [r, show k - 1 - 1 = k - 2 by omega,
      Nat.cast_sub (show 1 ≤ k by omega), Nat.cast_one] using descent
  · have ascent := tail_ascent_numeric thetaBounds hr scaleLtQ qUpper
    have boundNonneg : (0 : Real) ≤ tailGapBound q := by positivity
    have constantEffect : (tailGapBound q : Real) * mertens ≤
        (tailGapBound q : Real) * (2 / 3 : Real) :=
      mul_le_mul_of_nonneg_left mertens_le boundNonneg
    have expressionLe :
        (tailGapBound q : Real) *
            (Real.log (Real.log ((9 * primorial q : Nat) : Real)) + mertens +
              dusartReciprocalError (((9 * primorial q : Nat) : Real)) + 1) ≤
          (tailGapBound q : Real) *
            (Real.log (Real.log ((9 * primorial q : Nat) : Real)) + 2 / 3 +
              dusartReciprocalError (((9 * primorial q : Nat) : Real)) + 1) := by
      nlinarith
    exact expressionLe.trans_lt (by
      simpa only [r, Nat.cast_sub (show 1 ≤ k by omega), Nat.cast_one] using ascent)

end

end PrimeFactorUnimodality
