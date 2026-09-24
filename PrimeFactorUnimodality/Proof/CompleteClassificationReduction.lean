import PrimeFactorUnimodality.Proof.LargeRange.UniformTailClosedMertens

set_option autoImplicit false

/-! # Final classification reduction across the optimized finite/tail overlap

This focused assembly keeps the finite certificates out of its dependency
graph. Finite Abel summation and the Mertens upper bound leave only the three
prime-distribution inputs in the infinite tail, starting at `38001`.
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
    (finiteRange : ∀ k : Nat, 1 ≤ k → k ≤ 8600001 →
      (IsUnimodal (primeFactorDensity k) ↔ k ≤ 3))
    (primeCountingBounds : HasDusartPrimeCountingBounds)
    (thetaBounds : HasDusartThetaBounds)
    (tailPair : HasUniformTailPrimePair)
    (k : Nat) (hk : 1 ≤ k) :
    IsUnimodal (primeFactorDensity k) ↔ k ≤ 3 := by
  have classification := completeClassification_of_finite_range_and_tail
    8600001 (by omega) finiteRange (fun k hkTail =>
      uniformTail_not_isUnimodal_closed_mertens primeCountingBounds thetaBounds
        tailPair (k := k) (by omega))
  exact classification k hk

/-- Classification from the existing prefix through `38000` and the uniform
CRT tail. The full megagap is not an input to this assembly. -/
theorem completeClassification_of_finite_prefix_and_tailTheta
    (finiteRange : ∀ k : Nat, 1 ≤ k → k ≤ 38000 →
      (IsUnimodal (primeFactorDensity k) ↔ k ≤ 3))
    (primeCountingBounds : HasDusartPrimeCountingBounds)
    (thetaBounds : HasTailThetaBounds)
    (tailPair : HasUniformTailPrimePair) : CompleteClassification := by
  exact completeClassification_of_finite_range_and_tail
    38000 (by omega) finiteRange (fun k hkTail =>
      uniformTail_not_isUnimodal_of_tailTheta primeCountingBounds thetaBounds
        tailPair (k := k) (by omega))

/-- Preserve the original public analytic interface while using the weaker
theta requirements internally. -/
theorem completeClassification_of_finite_prefix_and_primeCounting
    (finiteRange : ∀ k : Nat, 1 ≤ k → k ≤ 38000 →
      (IsUnimodal (primeFactorDensity k) ↔ k ≤ 3))
    (primeCountingBounds : HasDusartPrimeCountingBounds)
    (thetaBounds : HasDusartThetaBounds)
    (tailPair : HasUniformTailPrimePair) : CompleteClassification :=
  completeClassification_of_finite_prefix_and_tailTheta finiteRange primeCountingBounds
    (hasTailThetaBounds_of_dusart thetaBounds) tailPair

/-- A log-square theta error and a finite prefix suffice in place of the
stronger theta package. The prime-counting and short-interval obligations
remain explicit, as does the finite classification. -/
theorem completeClassification_of_finite_prefix_and_logSquared
    (finiteRange : ∀ k : Nat, 1 ≤ k → k ≤ 38000 →
      (IsUnimodal (primeFactorDensity k) ↔ k ≤ 3))
    (primeCountingBounds : HasDusartPrimeCountingBounds)
    (thetaPrefix : ∀ q : Nat, 3501 ≤ q → q < 3594641 → TailThetaAt q)
    (thetaError : HasThetaLogSquaredError (1 / 5) 3594641)
    (shortInterval : HasDusartShortIntervalPrime) : CompleteClassification :=
  completeClassification_of_finite_prefix_and_tailTheta finiteRange primeCountingBounds
    (hasTailThetaBounds_of_logSquared thetaPrefix thetaError)
    (hasUniformTailPrimePair_of_shortInterval shortInterval)

end

end PrimeFactorUnimodality
