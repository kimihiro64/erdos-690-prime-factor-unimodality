/-
Copyright (c) 2026 kimihiro64. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kimihiro64
-/
module

public import Mathlib.Data.Nat.Prime.Basic

/-!
# Primality from congruences of prime divisors

This file gives an elementary final step used by partial-factorization
primality criteria.  If a modulus is larger than the square root of a number
and every prime divisor is congruent to either `1` or `-1` modulo that modulus,
then excluding the sole possible small divisor proves primality.
-/

public section

namespace Nat

/-- Suppose `n < F ^ 2` and every prime divisor `p` of `n` satisfies
`F ∣ p - 1` or `F ∣ p + 1`. If `F - 1` does not divide `n`, then `n` is
prime. -/
theorem prime_of_large_factor_dvd_sub_or_add {n F : ℕ} (hn : 1 < n)
    (hlarge : n < F ^ 2)
    (hdivisors : ∀ p : ℕ, p.Prime → p ∣ n → F ∣ p - 1 ∨ F ∣ p + 1)
    (hexclude : ¬F - 1 ∣ n) : n.Prime := by
  by_contra hnPrime
  have hnPos : 0 < n := by omega
  let p := n.minFac
  have hpPrime : p.Prime := Nat.minFac_prime (by omega)
  have hpTwo : 2 ≤ p := hpPrime.two_le
  have hpDvd : p ∣ n := Nat.minFac_dvd n
  have hpSq : p ^ 2 ≤ n := Nat.minFac_sq_le_self hnPos hnPrime
  have hpLtF : p < F := by
    by_contra h
    have hFLeP : F ≤ p := by omega
    have : F ^ 2 ≤ p ^ 2 := Nat.pow_le_pow_left hFLeP 2
    omega
  rcases hdivisors p hpPrime hpDvd with hsub | hadd
  · have hFLe : F ≤ p - 1 := Nat.le_of_dvd (by omega) hsub
    omega
  · have hFLe : F ≤ p + 1 := Nat.le_of_dvd (by omega) hadd
    have hpSucc : p + 1 = F := by omega
    have hpred : F - 1 = p := by omega
    apply hexclude
    simpa [hpred] using hpDvd

end Nat
