import PrimeFactorUnimodality.Proof.LargeRange.ClosedMertensTailBounds
import PrimeFactorUnimodality.Proof.LargeRange.ClosedMertensUniformReduction
import PrimeFactorUnimodality.Proof.LargeRange.TailPrimeCountingBounds

set_option autoImplicit false

/-! # Uniform tail with reciprocal-prime input closed

From the optimized overlap with the full record-gap range, the proved Mertens
estimate replaces the conditional sharp reciprocal-prime interface.
-/

namespace PrimeFactorUnimodality

noncomputable section

theorem uniformTail_not_isUnimodal_closed_mertens
    (primeCountingBounds : HasDusartPrimeCountingBounds)
    (thetaBounds : HasDusartThetaBounds)
    (tailPair : HasUniformTailPrimePair)
    {k : Nat} (hk : 7300001 ≤ k) :
    ¬ IsUnimodal (primeFactorDensity k) := by
  let r := k - 1
  have hr : 7300000 ≤ r := by dsimp only [r]; omega
  have hrBase : 38000 ≤ r := by omega
  obtain ⟨qPrev, q, consecutive, prevLarge, scaleLtQ, qUpper, scalePrev⟩ :=
    tailPair r hrBase
  apply uniformConstruction_not_isUnimodal_of_closed_mertens_direct
    primeCountingBounds consecutive
  · exact tail_predecessor_gt_two (by omega : 3301 ≤ qPrev)
  · omega
  · exact tailGapBound_pos q
  · exact tail_primorial_large hrBase scaleLtQ
  · exact tail_primeCounting_shell_numeric thetaBounds hrBase scaleLtQ qUpper
  · simpa only [r, Nat.sub_add_cancel (show 1 ≤ k by omega)] using
      tail_descentDefined primeCountingBounds thetaBounds hrBase scaleLtQ
  · have hprefix := tail_prefix_le_primorial
      primeCountingBounds thetaBounds hrBase scaleLtQ
    simpa only [r, show k - 1 - 1 = k - 2 by omega] using hprefix
  · have descent := tail_descent_numeric_closed_mertens
      thetaBounds primeCountingBounds hr scaleLtQ scalePrev
    simpa only [r, show k - 1 - 1 = k - 2 by omega,
      Nat.cast_sub (show 1 ≤ k by omega), Nat.cast_one] using descent
  · have ascent := tail_ascent_numeric_closed_mertens
      thetaBounds hr scaleLtQ qUpper
    simpa only [r, Nat.cast_sub (show 1 ≤ k by omega), Nat.cast_one] using ascent

end

end PrimeFactorUnimodality
