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

/-! A reusable finite/tail assembly.  The cutoff is an explicit parameter so
future record-range improvements do not change the universal theorem's
logical shape. -/
theorem completeClassification_of_finite_range_and_tail
    (cutoff : Nat) (hcutoff : 3 ≤ cutoff)
    (finiteRange : ∀ k : Nat, 1 ≤ k → k ≤ cutoff →
      (IsUnimodal (primeFactorDensity k) ↔ k ≤ 3))
    (tail : ∀ k : Nat, cutoff < k → ¬ IsUnimodal (primeFactorDensity k)) :
    CompleteClassification := by
  intro k hk
  by_cases hkFinite : k ≤ cutoff
  · exact finiteRange k hk hkFinite
  · constructor
    · intro unimodal
      exact (tail k (by omega)) unimodal |>.elim
    · intro hkThree
      omega

theorem completeClassification_of_finite_record_range
    (finiteRange : ∀ k : Nat, 1 ≤ k → k ≤ 7400000 →
      (IsUnimodal (primeFactorDensity k) ↔ k ≤ 3))
    (primeCountingBounds : HasDusartPrimeCountingBounds)
    (thetaBounds : HasDusartThetaBounds)
    (shortInterval : HasDusartShortIntervalPrime)
    (k : Nat) (hk : 1 ≤ k) :
    IsUnimodal (primeFactorDensity k) ↔ k ≤ 3 := by
  have classification := completeClassification_of_finite_range_and_tail
    7400000 (by omega) finiteRange (fun k hkTail =>
      uniformTail_not_isUnimodal_closed_mertens primeCountingBounds thetaBounds
        shortInterval (k := k) (by omega))
  exact classification k hk

end

end PrimeFactorUnimodality
