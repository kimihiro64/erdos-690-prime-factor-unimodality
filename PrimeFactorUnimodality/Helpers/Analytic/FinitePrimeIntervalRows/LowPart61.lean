import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowBase

set_option autoImplicit false
set_option maxRecDepth 100000

/-! # Lower finite Dusart prefix chunk 61 -/

namespace PrimeFactorUnimodality

noncomputable section
set_option maxHeartbeats 20000000 in
theorem lowPrime_7043 : Nat.Prime 7043 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 7043 7042 1 2 [2, 7, 503]
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
    · change IsUnit ((2 : ZMod 7043) ^ 3521 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (3521 : ZMod 7043)
      decide
    · change IsUnit ((2 : ZMod 7043) ^ 1006 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (686 : ZMod 7043)
      decide
    · change IsUnit ((2 : ZMod 7043) ^ 14 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (417 : ZMod 7043)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_7057 : Nat.Prime 7057 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 7057 7056 1 5 [2, 2, 2, 2, 3, 3, 7, 7]
  · norm_num
  · norm_num
  · norm_num
  · intro p hp
    simp at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals decide
  · norm_num
  · norm_num
  · rw [← natCast_fastPowMod_eq_pow]
    decide
  · intro q hq
    simp at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change IsUnit ((5 : ZMod 7057) ^ 3528 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (3528 : ZMod 7057)
      decide
    · change IsUnit ((5 : ZMod 7057) ^ 3528 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (3528 : ZMod 7057)
      decide
    · change IsUnit ((5 : ZMod 7057) ^ 3528 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (3528 : ZMod 7057)
      decide
    · change IsUnit ((5 : ZMod 7057) ^ 3528 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (3528 : ZMod 7057)
      decide
    · change IsUnit ((5 : ZMod 7057) ^ 2352 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (7008 : ZMod 7057)
      decide
    · change IsUnit ((5 : ZMod 7057) ^ 2352 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (7008 : ZMod 7057)
      decide
    · change IsUnit ((5 : ZMod 7057) ^ 1008 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (5029 : ZMod 7057)
      decide
    · change IsUnit ((5 : ZMod 7057) ^ 1008 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (5029 : ZMod 7057)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_7069 : Nat.Prime 7069 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 7069 7068 1 2 [2, 2, 3, 19, 31]
  · norm_num
  · norm_num
  · norm_num
  · intro p hp
    simp at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl
    all_goals decide
  · norm_num
  · norm_num
  · rw [← natCast_fastPowMod_eq_pow]
    decide
  · intro q hq
    simp at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · change IsUnit ((2 : ZMod 7069) ^ 3534 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (3534 : ZMod 7069)
      decide
    · change IsUnit ((2 : ZMod 7069) ^ 3534 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (3534 : ZMod 7069)
      decide
    · change IsUnit ((2 : ZMod 7069) ^ 2356 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (3036 : ZMod 7069)
      decide
    · change IsUnit ((2 : ZMod 7069) ^ 372 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (1821 : ZMod 7069)
      decide
    · change IsUnit ((2 : ZMod 7069) ^ 228 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (2187 : ZMod 7069)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_7079 : Nat.Prime 7079 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 7079 7078 1 7 [2, 3539]
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
    · change IsUnit ((7 : ZMod 7079) ^ 3539 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (3539 : ZMod 7079)
      decide
    · change IsUnit ((7 : ZMod 7079) ^ 2 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (3687 : ZMod 7079)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_7103 : Nat.Prime 7103 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 7103 7102 1 5 [2, 53, 67]
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
    · change IsUnit ((5 : ZMod 7103) ^ 3551 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (3551 : ZMod 7103)
      decide
    · change IsUnit ((5 : ZMod 7103) ^ 134 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (5310 : ZMod 7103)
      decide
    · change IsUnit ((5 : ZMod 7103) ^ 106 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (131 : ZMod 7103)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_7109 : Nat.Prime 7109 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 7109 7108 1 2 [2, 2, 1777]
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
    · change IsUnit ((2 : ZMod 7109) ^ 3554 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (3554 : ZMod 7109)
      decide
    · change IsUnit ((2 : ZMod 7109) ^ 3554 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (3554 : ZMod 7109)
      decide
    · change IsUnit ((2 : ZMod 7109) ^ 4 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (474 : ZMod 7109)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_7121 : Nat.Prime 7121 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 7121 7120 1 3 [2, 2, 2, 2, 5, 89]
  · norm_num
  · norm_num
  · norm_num
  · intro p hp
    simp at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl
    all_goals decide
  · norm_num
  · norm_num
  · rw [← natCast_fastPowMod_eq_pow]
    decide
  · intro q hq
    simp at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · change IsUnit ((3 : ZMod 7121) ^ 3560 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (3560 : ZMod 7121)
      decide
    · change IsUnit ((3 : ZMod 7121) ^ 3560 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (3560 : ZMod 7121)
      decide
    · change IsUnit ((3 : ZMod 7121) ^ 3560 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (3560 : ZMod 7121)
      decide
    · change IsUnit ((3 : ZMod 7121) ^ 3560 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (3560 : ZMod 7121)
      decide
    · change IsUnit ((3 : ZMod 7121) ^ 1424 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (68 : ZMod 7121)
      decide
    · change IsUnit ((3 : ZMod 7121) ^ 80 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (2793 : ZMod 7121)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_7127 : Nat.Prime 7127 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 7127 7126 1 5 [2, 7, 509]
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
    · change IsUnit ((5 : ZMod 7127) ^ 3563 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (3563 : ZMod 7127)
      decide
    · change IsUnit ((5 : ZMod 7127) ^ 1018 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (4943 : ZMod 7127)
      decide
    · change IsUnit ((5 : ZMod 7127) ^ 14 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (331 : ZMod 7127)
      decide
  · norm_num
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_6977_7332_part02 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_7331 (p := 7039) (q := 7043) (by exact lowPrime_7043) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_7331 (p := 7043) (q := 7057) (by exact lowPrime_7057) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_7331 (p := 7057) (q := 7069) (by exact lowPrime_7069) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_7331 (p := 7069) (q := 7079) (by exact lowPrime_7079) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_7331 (p := 7079) (q := 7103) (by exact lowPrime_7103) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_7331 (p := 7103) (q := 7109) (by exact lowPrime_7109) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_7331 (p := 7109) (q := 7121) (by exact lowPrime_7121) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_7331 (p := 7121) (q := 7127) (by exact lowPrime_7127) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_6977_7332_part02_chain :
    DusartPrimeRowsChain 7039 7127 dusartPrimeRows_6977_7332_part02 := by
  apply DusartPrimeRowsChain.cons
  · norm_num [dusartPrimeRow_of_explicit_7331]
  · norm_num [dusartPrimeRow_of_explicit_7331]
  · apply DusartPrimeRowsChain.cons
    · norm_num [dusartPrimeRow_of_explicit_7331]
    · norm_num [dusartPrimeRow_of_explicit_7331]
    · apply DusartPrimeRowsChain.cons
      · norm_num [dusartPrimeRow_of_explicit_7331]
      · norm_num [dusartPrimeRow_of_explicit_7331]
      · apply DusartPrimeRowsChain.cons
        · norm_num [dusartPrimeRow_of_explicit_7331]
        · norm_num [dusartPrimeRow_of_explicit_7331]
        · apply DusartPrimeRowsChain.cons
          · norm_num [dusartPrimeRow_of_explicit_7331]
          · norm_num [dusartPrimeRow_of_explicit_7331]
          · apply DusartPrimeRowsChain.cons
            · norm_num [dusartPrimeRow_of_explicit_7331]
            · norm_num [dusartPrimeRow_of_explicit_7331]
            · apply DusartPrimeRowsChain.cons
              · norm_num [dusartPrimeRow_of_explicit_7331]
              · norm_num [dusartPrimeRow_of_explicit_7331]
              · apply DusartPrimeRowsChain.cons
                · norm_num [dusartPrimeRow_of_explicit_7331]
                · norm_num [dusartPrimeRow_of_explicit_7331]
                · apply DusartPrimeRowsChain.empty
                  norm_num
