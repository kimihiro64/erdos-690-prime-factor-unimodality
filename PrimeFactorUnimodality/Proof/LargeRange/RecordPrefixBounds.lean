import Mathlib.Analysis.Complex.ExponentialBounds
import PrimeFactorUnimodality.Helpers.PrimeSequence.AverageGap
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordPrimeWitnesses

set_option autoImplicit false

/-! # Bounds for the prime prefix in the record-input range -/

namespace PrimeFactorUnimodality

noncomputable section

private theorem log_500000_lt :
    Real.log 500000 < (1313 : Real) / 100 := by
  have powerLt : (500000 : Real) ^ 2 < 2 ^ 3 * 3 ^ 22 := by norm_num
  have logged := Real.log_lt_log (by positivity) powerLt
  rw [Real.log_pow, Real.log_mul (by positivity) (by positivity),
    Real.log_pow, Real.log_pow] at logged
  norm_num at logged ⊢
  nlinarith [Real.log_two_lt_d9, Real.log_three_lt_d9]

/-- A finite, kernel-checked prime-count certificate at the only cutoff used
by the record construction. -/
theorem record_primeCounting_500001_ge :
    38000 ≤ Nat.primeCounting' 500001 := by
  rw [← Nat.primesBelow_card_eq_primeCounting']
  rw [← recordPrimeWitnesses_card]
  exact Finset.card_le_card recordPrimeWitnesses_subset

theorem record_prefix_primeAt_le_500000
    {k : Nat} (hk : k ≤ 38001) :
    primeAt (k - 2) ≤ 500000 := by
  apply primeAt_le_of_succ_le_primeCounting'
  exact (show k - 2 + 1 ≤ 38000 by omega).trans
    record_primeCounting_500001_ge

private theorem log_1313_div_100_lt :
    Real.log ((1313 : Real) / 100) < (258 : Real) / 100 := by
  have powerLt : ((1313 : Real) / 100) ^ 5 < 2 ^ 17 * 3 := by norm_num
  have logged := Real.log_lt_log (by positivity) powerLt
  rw [Real.log_pow, Real.log_mul (by positivity) (by positivity),
    Real.log_pow] at logged
  norm_num at logged ⊢
  nlinarith [Real.log_two_lt_d9, Real.log_three_lt_d9]

theorem record_prefix_log_log_lt
    {k : Nat} (hkLower : 49 ≤ k) (hkUpper : k ≤ 38000) :
    Real.log (Real.log ((primeAt (k - 2) - 1 : Nat) : Real)) <
      (258 : Real) / 100 := by
  have prefixLarge : 2 ≤ primeAt (k - 2) - 1 := by
    have primeFive : 5 ≤ primeAt (k - 2) := by
      have indexTwo : 2 ≤ k - 2 := by omega
      have := primeAt_strictMono.monotone indexTwo
      norm_num [primeAt] at this ⊢
      exact this
    omega
  have prefixLe : primeAt (k - 2) - 1 ≤ 500000 :=
    (Nat.sub_le _ _).trans
      (record_prefix_primeAt_le_500000 (by omega))
  have innerPos : 0 < Real.log ((primeAt (k - 2) - 1 : Nat) : Real) :=
    Real.log_pos (by exact_mod_cast (show 1 < primeAt (k - 2) - 1 by omega))
  have innerLt :
      Real.log ((primeAt (k - 2) - 1 : Nat) : Real) < (1313 : Real) / 100 :=
    (Real.log_le_log (by exact_mod_cast (show 0 < primeAt (k - 2) - 1 by omega))
      (by exact_mod_cast prefixLe)).trans_lt log_500000_lt
  exact (Real.log_lt_log innerPos innerLt).trans log_1313_div_100_lt

end

end PrimeFactorUnimodality
