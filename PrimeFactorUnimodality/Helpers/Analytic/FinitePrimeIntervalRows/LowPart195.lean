import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowBase

set_option autoImplicit false
set_option maxRecDepth 100000

/-! # Lower finite Dusart prefix chunk 195 -/

namespace PrimeFactorUnimodality

noncomputable section
set_option maxHeartbeats 20000000 in
theorem lowPrime_16481 : Nat.Prime 16481 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 16481 16480 1 6 [2, 2, 2, 2, 2, 5, 103]
  · norm_num
  · norm_num
  · norm_num
  · intro p hp
    simp at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals decide
  · norm_num
  · norm_num
  · rw [← natCast_fastPowMod_eq_pow]
    decide
  · intro q hq
    simp at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change IsUnit ((6 : ZMod 16481) ^ 8240 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (8240 : ZMod 16481)
      decide
    · change IsUnit ((6 : ZMod 16481) ^ 8240 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (8240 : ZMod 16481)
      decide
    · change IsUnit ((6 : ZMod 16481) ^ 8240 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (8240 : ZMod 16481)
      decide
    · change IsUnit ((6 : ZMod 16481) ^ 8240 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (8240 : ZMod 16481)
      decide
    · change IsUnit ((6 : ZMod 16481) ^ 8240 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (8240 : ZMod 16481)
      decide
    · change IsUnit ((6 : ZMod 16481) ^ 3296 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (16210 : ZMod 16481)
      decide
    · change IsUnit ((6 : ZMod 16481) ^ 160 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (9751 : ZMod 16481)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_16487 : Nat.Prime 16487 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 16487 16486 1 5 [2, 8243]
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
    · change IsUnit ((5 : ZMod 16487) ^ 8243 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (8243 : ZMod 16487)
      decide
    · change IsUnit ((5 : ZMod 16487) ^ 2 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (687 : ZMod 16487)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_16493 : Nat.Prime 16493 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 16493 16492 1 2 [2, 2, 7, 19, 31]
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
    · change IsUnit ((2 : ZMod 16493) ^ 8246 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (8246 : ZMod 16493)
      decide
    · change IsUnit ((2 : ZMod 16493) ^ 8246 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (8246 : ZMod 16493)
      decide
    · change IsUnit ((2 : ZMod 16493) ^ 2356 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (4947 : ZMod 16493)
      decide
    · change IsUnit ((2 : ZMod 16493) ^ 868 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (15673 : ZMod 16493)
      decide
    · change IsUnit ((2 : ZMod 16493) ^ 532 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (14885 : ZMod 16493)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_16519 : Nat.Prime 16519 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 16519 16518 1 3 [2, 3, 2753]
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
    · change IsUnit ((3 : ZMod 16519) ^ 8259 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (8259 : ZMod 16519)
      decide
    · change IsUnit ((3 : ZMod 16519) ^ 5506 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (9191 : ZMod 16519)
      decide
    · change IsUnit ((3 : ZMod 16519) ^ 6 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (15271 : ZMod 16519)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_16529 : Nat.Prime 16529 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 16529 16528 1 3 [2, 2, 2, 2, 1033]
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
    · change IsUnit ((3 : ZMod 16529) ^ 8264 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (8264 : ZMod 16529)
      decide
    · change IsUnit ((3 : ZMod 16529) ^ 8264 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (8264 : ZMod 16529)
      decide
    · change IsUnit ((3 : ZMod 16529) ^ 8264 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (8264 : ZMod 16529)
      decide
    · change IsUnit ((3 : ZMod 16529) ^ 8264 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (8264 : ZMod 16529)
      decide
    · change IsUnit ((3 : ZMod 16529) ^ 16 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (721 : ZMod 16529)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_16547 : Nat.Prime 16547 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 16547 16546 1 2 [2, 8273]
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
    · change IsUnit ((2 : ZMod 16547) ^ 8273 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (8273 : ZMod 16547)
      decide
    · change IsUnit ((2 : ZMod 16547) ^ 2 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (5516 : ZMod 16547)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_16553 : Nat.Prime 16553 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 16553 16552 1 3 [2, 2, 2, 2069]
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
    · change IsUnit ((3 : ZMod 16553) ^ 8276 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (8276 : ZMod 16553)
      decide
    · change IsUnit ((3 : ZMod 16553) ^ 8276 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (8276 : ZMod 16553)
      decide
    · change IsUnit ((3 : ZMod 16553) ^ 8276 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (8276 : ZMod 16553)
      decide
    · change IsUnit ((3 : ZMod 16553) ^ 8 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (9142 : ZMod 16553)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_16561 : Nat.Prime 16561 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 16561 16560 1 7 [2, 2, 2, 2, 3, 3, 5, 23]
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
    · change IsUnit ((7 : ZMod 16561) ^ 8280 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (8280 : ZMod 16561)
      decide
    · change IsUnit ((7 : ZMod 16561) ^ 8280 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (8280 : ZMod 16561)
      decide
    · change IsUnit ((7 : ZMod 16561) ^ 8280 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (8280 : ZMod 16561)
      decide
    · change IsUnit ((7 : ZMod 16561) ^ 8280 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (8280 : ZMod 16561)
      decide
    · change IsUnit ((7 : ZMod 16561) ^ 5520 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (12192 : ZMod 16561)
      decide
    · change IsUnit ((7 : ZMod 16561) ^ 5520 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (12192 : ZMod 16561)
      decide
    · change IsUnit ((7 : ZMod 16561) ^ 3312 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (9424 : ZMod 16561)
      decide
    · change IsUnit ((7 : ZMod 16561) ^ 720 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (11263 : ZMod 16561)
      decide
  · norm_num
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_16319_17158_part03 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_17154 (p := 16477) (q := 16481) (by exact lowPrime_16481) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_17154 (p := 16481) (q := 16487) (by exact lowPrime_16487) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_17154 (p := 16487) (q := 16493) (by exact lowPrime_16493) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_17154 (p := 16493) (q := 16519) (by exact lowPrime_16519) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_17154 (p := 16519) (q := 16529) (by exact lowPrime_16529) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_17154 (p := 16529) (q := 16547) (by exact lowPrime_16547) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_17154 (p := 16547) (q := 16553) (by exact lowPrime_16553) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_17154 (p := 16553) (q := 16561) (by exact lowPrime_16561) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_16319_17158_part03_chain :
    DusartPrimeRowsChain 16477 16561 dusartPrimeRows_16319_17158_part03 := by
  apply DusartPrimeRowsChain.cons
  · norm_num [dusartPrimeRow_of_explicit_17154]
  · norm_num [dusartPrimeRow_of_explicit_17154]
  · apply DusartPrimeRowsChain.cons
    · norm_num [dusartPrimeRow_of_explicit_17154]
    · norm_num [dusartPrimeRow_of_explicit_17154]
    · apply DusartPrimeRowsChain.cons
      · norm_num [dusartPrimeRow_of_explicit_17154]
      · norm_num [dusartPrimeRow_of_explicit_17154]
      · apply DusartPrimeRowsChain.cons
        · norm_num [dusartPrimeRow_of_explicit_17154]
        · norm_num [dusartPrimeRow_of_explicit_17154]
        · apply DusartPrimeRowsChain.cons
          · norm_num [dusartPrimeRow_of_explicit_17154]
          · norm_num [dusartPrimeRow_of_explicit_17154]
          · apply DusartPrimeRowsChain.cons
            · norm_num [dusartPrimeRow_of_explicit_17154]
            · norm_num [dusartPrimeRow_of_explicit_17154]
            · apply DusartPrimeRowsChain.cons
              · norm_num [dusartPrimeRow_of_explicit_17154]
              · norm_num [dusartPrimeRow_of_explicit_17154]
              · apply DusartPrimeRowsChain.cons
                · norm_num [dusartPrimeRow_of_explicit_17154]
                · norm_num [dusartPrimeRow_of_explicit_17154]
                · apply DusartPrimeRowsChain.empty
                  norm_num
