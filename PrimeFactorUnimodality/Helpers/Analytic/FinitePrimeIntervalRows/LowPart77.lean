import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowBase

set_option autoImplicit false
set_option maxRecDepth 100000

/-! # Lower finite Dusart prefix chunk 77 -/

namespace PrimeFactorUnimodality

noncomputable section
set_option maxHeartbeats 20000000 in
theorem lowPrime_8117 : Nat.Prime 8117 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 8117 8116 1 2 [2, 2, 2029]
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
    · change IsUnit ((2 : ZMod 8117) ^ 4058 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (4058 : ZMod 8117)
      decide
    · change IsUnit ((2 : ZMod 8117) ^ 4058 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (4058 : ZMod 8117)
      decide
    · change IsUnit ((2 : ZMod 8117) ^ 4 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (3788 : ZMod 8117)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_8123 : Nat.Prime 8123 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 8123 8122 1 2 [2, 31, 131]
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
    · change IsUnit ((2 : ZMod 8123) ^ 4061 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (4061 : ZMod 8123)
      decide
    · change IsUnit ((2 : ZMod 8123) ^ 262 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (3866 : ZMod 8123)
      decide
    · change IsUnit ((2 : ZMod 8123) ^ 62 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (7709 : ZMod 8123)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_8147 : Nat.Prime 8147 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 8147 8146 1 2 [2, 4073]
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
    · change IsUnit ((2 : ZMod 8147) ^ 4073 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (4073 : ZMod 8147)
      decide
    · change IsUnit ((2 : ZMod 8147) ^ 2 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (2716 : ZMod 8147)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_8161 : Nat.Prime 8161 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 8161 8160 1 7 [2, 2, 2, 2, 2, 3, 5, 17]
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
    · change IsUnit ((7 : ZMod 8161) ^ 4080 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (4080 : ZMod 8161)
      decide
    · change IsUnit ((7 : ZMod 8161) ^ 4080 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (4080 : ZMod 8161)
      decide
    · change IsUnit ((7 : ZMod 8161) ^ 4080 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (4080 : ZMod 8161)
      decide
    · change IsUnit ((7 : ZMod 8161) ^ 4080 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (4080 : ZMod 8161)
      decide
    · change IsUnit ((7 : ZMod 8161) ^ 4080 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (4080 : ZMod 8161)
      decide
    · change IsUnit ((7 : ZMod 8161) ^ 2720 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (6408 : ZMod 8161)
      decide
    · change IsUnit ((7 : ZMod 8161) ^ 1632 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (2231 : ZMod 8161)
      decide
    · change IsUnit ((7 : ZMod 8161) ^ 480 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (2310 : ZMod 8161)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_8167 : Nat.Prime 8167 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 8167 8166 1 3 [2, 3, 1361]
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
    · change IsUnit ((3 : ZMod 8167) ^ 4083 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (4083 : ZMod 8167)
      decide
    · change IsUnit ((3 : ZMod 8167) ^ 2722 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (1691 : ZMod 8167)
      decide
    · change IsUnit ((3 : ZMod 8167) ^ 6 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (7191 : ZMod 8167)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_8171 : Nat.Prime 8171 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 8171 8170 1 2 [2, 5, 19, 43]
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
    · change IsUnit ((2 : ZMod 8171) ^ 4085 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (4085 : ZMod 8171)
      decide
    · change IsUnit ((2 : ZMod 8171) ^ 1634 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (5060 : ZMod 8171)
      decide
    · change IsUnit ((2 : ZMod 8171) ^ 430 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (383 : ZMod 8171)
      decide
    · change IsUnit ((2 : ZMod 8171) ^ 190 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (7581 : ZMod 8171)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_8179 : Nat.Prime 8179 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 8179 8178 1 2 [2, 3, 29, 47]
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
    · change IsUnit ((2 : ZMod 8179) ^ 4089 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (4089 : ZMod 8179)
      decide
    · change IsUnit ((2 : ZMod 8179) ^ 2726 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (7813 : ZMod 8179)
      decide
    · change IsUnit ((2 : ZMod 8179) ^ 282 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (6725 : ZMod 8179)
      decide
    · change IsUnit ((2 : ZMod 8179) ^ 174 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (3326 : ZMod 8179)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_8191 : Nat.Prime 8191 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 8191 8190 1 17 [2, 3, 3, 5, 7, 13]
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
    · change IsUnit ((17 : ZMod 8191) ^ 4095 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (4095 : ZMod 8191)
      decide
    · change IsUnit ((17 : ZMod 8191) ^ 2730 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (2760 : ZMod 8191)
      decide
    · change IsUnit ((17 : ZMod 8191) ^ 2730 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (2760 : ZMod 8191)
      decide
    · change IsUnit ((17 : ZMod 8191) ^ 1638 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (2653 : ZMod 8191)
      decide
    · change IsUnit ((17 : ZMod 8191) ^ 1170 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (3806 : ZMod 8191)
      decide
    · change IsUnit ((17 : ZMod 8191) ^ 630 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (7021 : ZMod 8191)
      decide
  · norm_num
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_8111_8520_part01 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_8518 (p := 8111) (q := 8117) (by exact lowPrime_8117) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8518 (p := 8117) (q := 8123) (by exact lowPrime_8123) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8518 (p := 8123) (q := 8147) (by exact lowPrime_8147) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8518 (p := 8147) (q := 8161) (by exact lowPrime_8161) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8518 (p := 8161) (q := 8167) (by exact lowPrime_8167) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8518 (p := 8167) (q := 8171) (by exact lowPrime_8171) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8518 (p := 8171) (q := 8179) (by exact lowPrime_8179) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8518 (p := 8179) (q := 8191) (by exact lowPrime_8191) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_8111_8520_part01_chain :
    DusartPrimeRowsChain 8111 8191 dusartPrimeRows_8111_8520_part01 := by
  apply DusartPrimeRowsChain.cons
  · norm_num [dusartPrimeRow_of_explicit_8518]
  · norm_num [dusartPrimeRow_of_explicit_8518]
  · apply DusartPrimeRowsChain.cons
    · norm_num [dusartPrimeRow_of_explicit_8518]
    · norm_num [dusartPrimeRow_of_explicit_8518]
    · apply DusartPrimeRowsChain.cons
      · norm_num [dusartPrimeRow_of_explicit_8518]
      · norm_num [dusartPrimeRow_of_explicit_8518]
      · apply DusartPrimeRowsChain.cons
        · norm_num [dusartPrimeRow_of_explicit_8518]
        · norm_num [dusartPrimeRow_of_explicit_8518]
        · apply DusartPrimeRowsChain.cons
          · norm_num [dusartPrimeRow_of_explicit_8518]
          · norm_num [dusartPrimeRow_of_explicit_8518]
          · apply DusartPrimeRowsChain.cons
            · norm_num [dusartPrimeRow_of_explicit_8518]
            · norm_num [dusartPrimeRow_of_explicit_8518]
            · apply DusartPrimeRowsChain.cons
              · norm_num [dusartPrimeRow_of_explicit_8518]
              · norm_num [dusartPrimeRow_of_explicit_8518]
              · apply DusartPrimeRowsChain.cons
                · norm_num [dusartPrimeRow_of_explicit_8518]
                · norm_num [dusartPrimeRow_of_explicit_8518]
                · apply DusartPrimeRowsChain.empty
                  norm_num
