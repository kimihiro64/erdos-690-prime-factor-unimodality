import PrimeFactorUnimodality.Proof.LargeRange.UniformTailClosedMertens

set_option autoImplicit false

/-! # Final classification reduction across the optimized finite/tail overlap

This focused assembly theorem keeps the expensive finite certificates out of
the dependency graph.  Once their range reaches the source cutoff, the proved
Mertens estimate means that only the three prime-distribution inputs remain in
the infinite tail.
-/

namespace PrimeFactorUnimodality

noncomputable section

theorem completeClassification_of_finite_record_range
    (finiteRange : ∀ k : Nat, 1 ≤ k → k ≤ 7300000 →
      (IsUnimodal (primeFactorDensity k) ↔ k ≤ 3))
    (primeCountingBounds : HasDusartPrimeCountingBounds)
    (thetaBounds : HasDusartThetaBounds)
    (shortInterval : HasDusartShortIntervalPrime)
    (k : Nat) (hk : 1 ≤ k) :
    IsUnimodal (primeFactorDensity k) ↔ k ≤ 3 := by
  by_cases hkFinite : k ≤ 7300000
  · have atK := finiteRange k
    have atPositive := atK hk
    exact atPositive hkFinite
  · constructor
    · intro unimodal
      exact ((uniformTail_not_isUnimodal_closed_mertens primeCountingBounds
        thetaBounds shortInterval (k := k) (by omega)) unimodal).elim
    · intro hkThree
      omega

end

end PrimeFactorUnimodality
