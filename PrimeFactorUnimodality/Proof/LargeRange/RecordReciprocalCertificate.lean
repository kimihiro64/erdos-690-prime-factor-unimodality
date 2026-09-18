import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordReciprocalBlocks

set_option autoImplicit false

/-! # Finite reciprocal-prime certificate for the record range -/

namespace PrimeFactorUnimodality

noncomputable section

private theorem reciprocal_le_rounded {p : Nat} (hp : p.Prime) :
    1 / (p : Real) ≤
      (roundedReciprocalNumerator p : Real) / reciprocalCertificateScale := by
  have pPos : 0 < p := hp.pos
  rw [div_le_div_iff₀ (by exact_mod_cast pPos)
    (by norm_num [reciprocalCertificateScale] :
      (0 : Real) < reciprocalCertificateScale)]
  norm_num only [one_mul]
  rw [mul_comm]
  exact_mod_cast (Nat.lt_mul_div_succ reciprocalCertificateScale pPos).le

/-- Exact finite upper bound used to close the last portion of the record
range without assuming a published reciprocal-prime estimate. -/
theorem reciprocalPrimeSumBelow_500001_lt :
    reciprocalPrimeSumBelow 500001 < (71 : Real) / 25 := by
  rw [reciprocalPrimeSumBelow]
  calc
    ∑ p ∈ Nat.primesBelow 500001, 1 / (p : Real) ≤
        ∑ p ∈ Nat.primesBelow 500001,
          (roundedReciprocalNumerator p : Real) /
            reciprocalCertificateScale := by
      apply Finset.sum_le_sum
      intro p hp
      exact reciprocal_le_rounded (Nat.prime_of_mem_primesBelow hp)
    _ ≤ ∑ p ∈ (Finset.range 500001).filter reciprocalSieveCandidate,
          (roundedReciprocalNumerator p : Real) /
            reciprocalCertificateScale := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro p hp
        rw [Nat.mem_primesBelow] at hp
        rw [Finset.mem_filter, Finset.mem_range]
        exact ⟨hp.1, prime_mem_reciprocalSieveCandidate hp.2⟩
      · intro p _ _
        positivity
    _ = (roundedReciprocalSieveSumBelow 500001 : Real) /
        reciprocalCertificateScale := by
      rw [roundedReciprocalSieveSumBelow]
      push_cast
      simp only [roundedReciprocalNumerator, reciprocalCertificateScale,
        Nat.cast_add, Nat.cast_one, Nat.cast_ofNat, div_eq_mul_inv,
        Finset.sum_mul]
    _ = (2838580130 : Real) / 1000000000 := by
      rw [roundedReciprocalSieveSumBelow_500001_eq]
      rfl
    _ < (71 : Real) / 25 := by norm_num

end

end PrimeFactorUnimodality
