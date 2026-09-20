import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowBase

set_option autoImplicit false
set_option maxRecDepth 100000

/-! # Lower finite Dusart prefix chunk 66 -/

namespace PrimeFactorUnimodality

noncomputable section
set_option maxHeartbeats 20000000 in
theorem lowPrime_7457 : Nat.Prime 7457 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 7457 7456 1 3 [2, 2, 2, 2, 2, 233]
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
    · change IsUnit ((3 : ZMod 7457) ^ 3728 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (3728 : ZMod 7457)
      decide
    · change IsUnit ((3 : ZMod 7457) ^ 3728 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (3728 : ZMod 7457)
      decide
    · change IsUnit ((3 : ZMod 7457) ^ 3728 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (3728 : ZMod 7457)
      decide
    · change IsUnit ((3 : ZMod 7457) ^ 3728 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (3728 : ZMod 7457)
      decide
    · change IsUnit ((3 : ZMod 7457) ^ 3728 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (3728 : ZMod 7457)
      decide
    · change IsUnit ((3 : ZMod 7457) ^ 32 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (4858 : ZMod 7457)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_7459 : Nat.Prime 7459 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 7459 7458 1 2 [2, 3, 11, 113]
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
    · change IsUnit ((2 : ZMod 7459) ^ 3729 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (3729 : ZMod 7459)
      decide
    · change IsUnit ((2 : ZMod 7459) ^ 2486 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (2562 : ZMod 7459)
      decide
    · change IsUnit ((2 : ZMod 7459) ^ 678 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (4094 : ZMod 7459)
      decide
    · change IsUnit ((2 : ZMod 7459) ^ 66 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (5218 : ZMod 7459)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_7477 : Nat.Prime 7477 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 7477 7476 1 2 [2, 2, 3, 7, 89]
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
    · change IsUnit ((2 : ZMod 7477) ^ 3738 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (3738 : ZMod 7477)
      decide
    · change IsUnit ((2 : ZMod 7477) ^ 3738 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (3738 : ZMod 7477)
      decide
    · change IsUnit ((2 : ZMod 7477) ^ 2492 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (3828 : ZMod 7477)
      decide
    · change IsUnit ((2 : ZMod 7477) ^ 1068 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (4413 : ZMod 7477)
      decide
    · change IsUnit ((2 : ZMod 7477) ^ 84 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (2010 : ZMod 7477)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_7481 : Nat.Prime 7481 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 7481 7480 1 6 [2, 2, 2, 5, 11, 17]
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
    · change IsUnit ((6 : ZMod 7481) ^ 3740 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (3740 : ZMod 7481)
      decide
    · change IsUnit ((6 : ZMod 7481) ^ 3740 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (3740 : ZMod 7481)
      decide
    · change IsUnit ((6 : ZMod 7481) ^ 3740 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (3740 : ZMod 7481)
      decide
    · change IsUnit ((6 : ZMod 7481) ^ 1496 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (1350 : ZMod 7481)
      decide
    · change IsUnit ((6 : ZMod 7481) ^ 680 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (1129 : ZMod 7481)
      decide
    · change IsUnit ((6 : ZMod 7481) ^ 440 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (2799 : ZMod 7481)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_7487 : Nat.Prime 7487 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 7487 7486 1 5 [2, 19, 197]
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
    · change IsUnit ((5 : ZMod 7487) ^ 3743 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (3743 : ZMod 7487)
      decide
    · change IsUnit ((5 : ZMod 7487) ^ 394 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (794 : ZMod 7487)
      decide
    · change IsUnit ((5 : ZMod 7487) ^ 38 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (2258 : ZMod 7487)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_7489 : Nat.Prime 7489 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 7489 7488 1 7 [2, 2, 2, 2, 2, 2, 3, 3, 13]
  · norm_num
  · norm_num
  · norm_num
  · intro p hp
    simp at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals decide
  · norm_num
  · norm_num
  · rw [← natCast_fastPowMod_eq_pow]
    decide
  · intro q hq
    simp at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change IsUnit ((7 : ZMod 7489) ^ 3744 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (3744 : ZMod 7489)
      decide
    · change IsUnit ((7 : ZMod 7489) ^ 3744 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (3744 : ZMod 7489)
      decide
    · change IsUnit ((7 : ZMod 7489) ^ 3744 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (3744 : ZMod 7489)
      decide
    · change IsUnit ((7 : ZMod 7489) ^ 3744 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (3744 : ZMod 7489)
      decide
    · change IsUnit ((7 : ZMod 7489) ^ 3744 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (3744 : ZMod 7489)
      decide
    · change IsUnit ((7 : ZMod 7489) ^ 3744 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (3744 : ZMod 7489)
      decide
    · change IsUnit ((7 : ZMod 7489) ^ 2496 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (822 : ZMod 7489)
      decide
    · change IsUnit ((7 : ZMod 7489) ^ 2496 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (822 : ZMod 7489)
      decide
    · change IsUnit ((7 : ZMod 7489) ^ 576 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (7432 : ZMod 7489)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_7499 : Nat.Prime 7499 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 7499 7498 1 2 [2, 23, 163]
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
    · change IsUnit ((2 : ZMod 7499) ^ 3749 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (3749 : ZMod 7499)
      decide
    · change IsUnit ((2 : ZMod 7499) ^ 326 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (1804 : ZMod 7499)
      decide
    · change IsUnit ((2 : ZMod 7499) ^ 46 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (646 : ZMod 7499)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_7507 : Nat.Prime 7507 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 7507 7506 1 2 [2, 3, 3, 3, 139]
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
    · change IsUnit ((2 : ZMod 7507) ^ 3753 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (3753 : ZMod 7507)
      decide
    · change IsUnit ((2 : ZMod 7507) ^ 2502 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (4802 : ZMod 7507)
      decide
    · change IsUnit ((2 : ZMod 7507) ^ 2502 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (4802 : ZMod 7507)
      decide
    · change IsUnit ((2 : ZMod 7507) ^ 2502 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (4802 : ZMod 7507)
      decide
    · change IsUnit ((2 : ZMod 7507) ^ 54 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (6606 : ZMod 7507)
      decide
  · norm_num
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_7333_7716_part02 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_7707 (p := 7451) (q := 7457) (by exact lowPrime_7457) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_7707 (p := 7457) (q := 7459) (by exact lowPrime_7459) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_7707 (p := 7459) (q := 7477) (by exact lowPrime_7477) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_7707 (p := 7477) (q := 7481) (by exact lowPrime_7481) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_7707 (p := 7481) (q := 7487) (by exact lowPrime_7487) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_7707 (p := 7487) (q := 7489) (by exact lowPrime_7489) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_7707 (p := 7489) (q := 7499) (by exact lowPrime_7499) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_7707 (p := 7499) (q := 7507) (by exact lowPrime_7507) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_7333_7716_part02_chain :
    DusartPrimeRowsChain 7451 7507 dusartPrimeRows_7333_7716_part02 := by
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
        · apply DusartPrimeRowsChain.cons
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
