import PrimeFactorUnimodality.Helpers.FiniteCertificates.ComputablePrimePrefix

set_option autoImplicit false

/-! # Reusing one finite prime prefix for many endpoint counts

The primality computation is checked once at the largest endpoint. All smaller
counts are obtained by filtering that proved list, without repeating the sieve.
-/

namespace PrimeFactorUnimodality

theorem primeCounting_eq_filter_length_of_prime_prefix
    {n N : Nat} (hn : n ≤ N) {ps : List Nat}
    (hps : computablePrimesBelow (N + 1) = ps) :
    Nat.primeCounting n = (ps.filter (fun p => decide (p ≤ n))).length := by
  subst ps
  rw [← computablePrimesBelow_succ_length]
  apply List.Perm.length_eq
  apply (List.perm_ext_iff_of_nodup
    (List.nodup_range.filter isPrimeTrial)
    ((List.nodup_range.filter isPrimeTrial).filter _)).2
  intro p
  simp only [computablePrimesBelow, List.mem_filter, List.mem_range,
    isPrimeTrial_eq_true_iff, decide_eq_true_eq]
  constructor
  · rintro ⟨hpn, hp⟩
    exact ⟨⟨by omega, hp⟩, by omega⟩
  · rintro ⟨⟨_, hp⟩, hpn⟩
    exact ⟨by omega, hp⟩

end PrimeFactorUnimodality
