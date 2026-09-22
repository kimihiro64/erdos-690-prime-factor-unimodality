import Mathlib.Analysis.Complex.ExponentialBounds
import PrimeFactorUnimodality.Helpers.Analytic.ExplicitPrimeCounting
import PrimeFactorUnimodality.Helpers.PrimeSequence.AverageGap

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

/-- The prime-counting input already needed for the infinite tail supplies
the record construction's prefix bound without enumerating prime witnesses. -/
theorem record_primeCounting_500001_ge :
    HasDusartPrimeCountingBounds → 38000 ≤ Nat.primeCounting' 500001 := by
  intro bounds
  have logPos : 0 < Real.log 500000 := Real.log_pos (by norm_num)
  have ratio : (38000 : Real) < 500000 / Real.log 500000 := by
    apply (lt_div_iff₀ logPos).2
    nlinarith [log_500000_lt]
  have lower := bounds.1 500000 (by norm_num)
  have correction : 0 ≤ (500000 / Real.log 500000) * (1 / Real.log 500000) :=
    by positivity
  unfold dusartPiLower at lower
  norm_num only [Nat.cast_ofNat] at lower
  have count : (38000 : Real) ≤ Nat.primeCounting 500000 := by nlinarith
  exact_mod_cast count

theorem record_prefix_primeAt_le_500000
    (bounds : HasDusartPrimeCountingBounds)
    {k : Nat} (hk : k ≤ 38001) :
    primeAt (k - 2) ≤ 500000 := by
  apply primeAt_le_of_succ_le_primeCounting'
  exact (show k - 2 + 1 ≤ 38000 by omega).trans
    (record_primeCounting_500001_ge bounds)

private theorem log_1313_div_100_lt :
    Real.log ((1313 : Real) / 100) < (258 : Real) / 100 := by
  have powerLt : ((1313 : Real) / 100) ^ 5 < 2 ^ 17 * 3 := by norm_num
  have logged := Real.log_lt_log (by positivity) powerLt
  rw [Real.log_pow, Real.log_mul (by positivity) (by positivity),
    Real.log_pow] at logged
  norm_num at logged ⊢
  nlinarith [Real.log_two_lt_d9, Real.log_three_lt_d9]

theorem record_prefix_log_log_lt
    (bounds : HasDusartPrimeCountingBounds)
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
      (record_prefix_primeAt_le_500000 bounds (by omega))
  have innerPos : 0 < Real.log ((primeAt (k - 2) - 1 : Nat) : Real) :=
    Real.log_pos (by exact_mod_cast (show 1 < primeAt (k - 2) - 1 by omega))
  have innerLt :
      Real.log ((primeAt (k - 2) - 1 : Nat) : Real) < (1313 : Real) / 100 :=
    (Real.log_le_log (by exact_mod_cast (show 0 < primeAt (k - 2) - 1 by omega))
      (by exact_mod_cast prefixLe)).trans_lt log_500000_lt
  exact (Real.log_lt_log innerPos innerLt).trans log_1313_div_100_lt

end

end PrimeFactorUnimodality
