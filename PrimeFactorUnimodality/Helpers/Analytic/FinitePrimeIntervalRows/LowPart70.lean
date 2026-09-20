import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowBase

set_option autoImplicit false
set_option maxRecDepth 100000

/-! # Lower finite Dusart prefix chunk 70 -/

namespace PrimeFactorUnimodality

noncomputable section
set_option maxHeartbeats 20000000 in
theorem lowPrime_7691 : Nat.Prime 7691 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 7691 7690 1 2 [2, 5, 769]
  · norm_num
  · norm_num
  · norm_num
  · intro p hp
    simp at hp
    rcases hp with rfl | rfl | rfl
    all_goals decide
  · norm_num
  · norm_num
  · rw [← natCast_fastPowMod_eq_pow]
    decide
  · intro q hq
    simp at hq
    rcases hq with rfl | rfl | rfl
    · change IsUnit ((2 : ZMod 7691) ^ 3845 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (3845 : ZMod 7691)
      decide
    · change IsUnit ((2 : ZMod 7691) ^ 1538 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (7630 : ZMod 7691)
      decide
    · change IsUnit ((2 : ZMod 7691) ^ 10 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (7067 : ZMod 7691)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_7699 : Nat.Prime 7699 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 7699 7698 1 3 [2, 3, 1283]
  · norm_num
  · norm_num
  · norm_num
  · intro p hp
    simp at hp
    rcases hp with rfl | rfl | rfl
    all_goals decide
  · norm_num
  · norm_num
  · rw [← natCast_fastPowMod_eq_pow]
    decide
  · intro q hq
    simp at hq
    rcases hq with rfl | rfl | rfl
    · change IsUnit ((3 : ZMod 7699) ^ 3849 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (3849 : ZMod 7699)
      decide
    · change IsUnit ((3 : ZMod 7699) ^ 2566 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (6942 : ZMod 7699)
      decide
    · change IsUnit ((3 : ZMod 7699) ^ 6 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (6229 : ZMod 7699)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_7703 : Nat.Prime 7703 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 7703 7702 1 5 [2, 3851]
  · norm_num
  · norm_num
  · norm_num
  · intro p hp
    simp at hp
    rcases hp with rfl | rfl
    all_goals decide
  · norm_num
  · norm_num
  · rw [← natCast_fastPowMod_eq_pow]
    decide
  · intro q hq
    simp at hq
    rcases hq with rfl | rfl
    · change IsUnit ((5 : ZMod 7703) ^ 3851 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (3851 : ZMod 7703)
      decide
    · change IsUnit ((5 : ZMod 7703) ^ 2 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (321 : ZMod 7703)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_7717 : Nat.Prime 7717 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 7717 7716 1 2 [2, 2, 3, 643]
  · norm_num
  · norm_num
  · norm_num
  · intro p hp
    simp at hp
    rcases hp with rfl | rfl | rfl | rfl
    all_goals decide
  · norm_num
  · norm_num
  · rw [← natCast_fastPowMod_eq_pow]
    decide
  · intro q hq
    simp at hq
    rcases hq with rfl | rfl | rfl | rfl
    · change IsUnit ((2 : ZMod 7717) ^ 3858 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (3858 : ZMod 7717)
      decide
    · change IsUnit ((2 : ZMod 7717) ^ 3858 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (3858 : ZMod 7717)
      decide
    · change IsUnit ((2 : ZMod 7717) ^ 2572 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (1146 : ZMod 7717)
      decide
    · change IsUnit ((2 : ZMod 7717) ^ 12 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (1191 : ZMod 7717)
      decide
  · norm_num
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_7333_7716_part06 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_7707 (p := 7687) (q := 7691) (by exact lowPrime_7691) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_7707 (p := 7691) (q := 7699) (by exact lowPrime_7699) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_7707 (p := 7699) (q := 7703) (by exact lowPrime_7703) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_7707 (p := 7703) (q := 7717) (by exact lowPrime_7717) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_7333_7716_part06_chain :
    DusartPrimeRowsChain 7687 7717 dusartPrimeRows_7333_7716_part06 := by
  apply DusartPrimeRowsChain.cons
  · norm_num [dusartPrimeRow_of_explicit_7707]
  · norm_num [dusartPrimeRow_of_explicit_7707]
  · apply DusartPrimeRowsChain.cons
    · norm_num [dusartPrimeRow_of_explicit_7707]
    · norm_num [dusartPrimeRow_of_explicit_7707]
    · apply DusartPrimeRowsChain.cons
      · norm_num [dusartPrimeRow_of_explicit_7707]
      · norm_num [dusartPrimeRow_of_explicit_7707]
      · apply DusartPrimeRowsChain.cons
        · norm_num [dusartPrimeRow_of_explicit_7707]
        · norm_num [dusartPrimeRow_of_explicit_7707]
        · apply DusartPrimeRowsChain.empty
          norm_num
