import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowBase

set_option autoImplicit false
set_option maxRecDepth 100000

/-! # Lower finite Dusart prefix chunk 226 -/

namespace PrimeFactorUnimodality

noncomputable section
set_option maxHeartbeats 20000000 in
theorem lowPrime_21517 : Nat.Prime 21517 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 21517 21516 1 5 [2, 2, 3, 11, 163]
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
    · change IsUnit ((5 : ZMod 21517) ^ 10758 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (10758 : ZMod 21517)
      decide
    · change IsUnit ((5 : ZMod 21517) ^ 10758 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (10758 : ZMod 21517)
      decide
    · change IsUnit ((5 : ZMod 21517) ^ 7172 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (13614 : ZMod 21517)
      decide
    · change IsUnit ((5 : ZMod 21517) ^ 1956 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (11203 : ZMod 21517)
      decide
    · change IsUnit ((5 : ZMod 21517) ^ 132 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (11816 : ZMod 21517)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_21521 : Nat.Prime 21521 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 21521 21520 1 3 [2, 2, 2, 2, 5, 269]
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
    · change IsUnit ((3 : ZMod 21521) ^ 10760 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (10760 : ZMod 21521)
      decide
    · change IsUnit ((3 : ZMod 21521) ^ 10760 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (10760 : ZMod 21521)
      decide
    · change IsUnit ((3 : ZMod 21521) ^ 10760 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (10760 : ZMod 21521)
      decide
    · change IsUnit ((3 : ZMod 21521) ^ 10760 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (10760 : ZMod 21521)
      decide
    · change IsUnit ((3 : ZMod 21521) ^ 4304 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (9195 : ZMod 21521)
      decide
    · change IsUnit ((3 : ZMod 21521) ^ 80 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (12060 : ZMod 21521)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_21523 : Nat.Prime 21523 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 21523 21522 1 2 [2, 3, 17, 211]
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
    · change IsUnit ((2 : ZMod 21523) ^ 10761 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (10761 : ZMod 21523)
      decide
    · change IsUnit ((2 : ZMod 21523) ^ 7174 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (10357 : ZMod 21523)
      decide
    · change IsUnit ((2 : ZMod 21523) ^ 1266 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (10195 : ZMod 21523)
      decide
    · change IsUnit ((2 : ZMod 21523) ^ 102 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (1610 : ZMod 21523)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_21529 : Nat.Prime 21529 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 21529 21528 1 11 [2, 2, 2, 3, 3, 13, 23]
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
    · change IsUnit ((11 : ZMod 21529) ^ 10764 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (10764 : ZMod 21529)
      decide
    · change IsUnit ((11 : ZMod 21529) ^ 10764 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (10764 : ZMod 21529)
      decide
    · change IsUnit ((11 : ZMod 21529) ^ 10764 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (10764 : ZMod 21529)
      decide
    · change IsUnit ((11 : ZMod 21529) ^ 7176 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (13028 : ZMod 21529)
      decide
    · change IsUnit ((11 : ZMod 21529) ^ 7176 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (13028 : ZMod 21529)
      decide
    · change IsUnit ((11 : ZMod 21529) ^ 1656 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (20321 : ZMod 21529)
      decide
    · change IsUnit ((11 : ZMod 21529) ^ 936 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (4011 : ZMod 21529)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_21557 : Nat.Prime 21557 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 21557 21556 1 2 [2, 2, 17, 317]
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
    · change IsUnit ((2 : ZMod 21557) ^ 10778 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (10778 : ZMod 21557)
      decide
    · change IsUnit ((2 : ZMod 21557) ^ 10778 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (10778 : ZMod 21557)
      decide
    · change IsUnit ((2 : ZMod 21557) ^ 1268 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (18082 : ZMod 21557)
      decide
    · change IsUnit ((2 : ZMod 21557) ^ 68 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (16310 : ZMod 21557)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_21559 : Nat.Prime 21559 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 21559 21558 1 15 [2, 3, 3593]
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
    · change IsUnit ((15 : ZMod 21559) ^ 10779 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (10779 : ZMod 21559)
      decide
    · change IsUnit ((15 : ZMod 21559) ^ 7186 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (1993 : ZMod 21559)
      decide
    · change IsUnit ((15 : ZMod 21559) ^ 6 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (20754 : ZMod 21559)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_21563 : Nat.Prime 21563 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 21563 21562 1 2 [2, 10781]
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
    · change IsUnit ((2 : ZMod 21563) ^ 10781 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (10781 : ZMod 21563)
      decide
    · change IsUnit ((2 : ZMod 21563) ^ 2 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (7188 : ZMod 21563)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_21569 : Nat.Prime 21569 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 21569 21568 1 3 [2, 2, 2, 2, 2, 2, 337]
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
    · change IsUnit ((3 : ZMod 21569) ^ 10784 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (10784 : ZMod 21569)
      decide
    · change IsUnit ((3 : ZMod 21569) ^ 10784 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (10784 : ZMod 21569)
      decide
    · change IsUnit ((3 : ZMod 21569) ^ 10784 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (10784 : ZMod 21569)
      decide
    · change IsUnit ((3 : ZMod 21569) ^ 10784 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (10784 : ZMod 21569)
      decide
    · change IsUnit ((3 : ZMod 21569) ^ 10784 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (10784 : ZMod 21569)
      decide
    · change IsUnit ((3 : ZMod 21569) ^ 10784 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (10784 : ZMod 21569)
      decide
    · change IsUnit ((3 : ZMod 21569) ^ 64 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (15354 : ZMod 21569)
      decide
  · norm_num
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_20959_22026_part08 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_22026 (p := 21503) (q := 21517) (by exact lowPrime_21517) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_22026 (p := 21517) (q := 21521) (by exact lowPrime_21521) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_22026 (p := 21521) (q := 21523) (by exact lowPrime_21523) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_22026 (p := 21523) (q := 21529) (by exact lowPrime_21529) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_22026 (p := 21529) (q := 21557) (by exact lowPrime_21557) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_22026 (p := 21557) (q := 21559) (by exact lowPrime_21559) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_22026 (p := 21559) (q := 21563) (by exact lowPrime_21563) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_22026 (p := 21563) (q := 21569) (by exact lowPrime_21569) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_20959_22026_part08_chain :
    DusartPrimeRowsChain 21503 21569 dusartPrimeRows_20959_22026_part08 := by
  apply DusartPrimeRowsChain.cons
  · norm_num [dusartPrimeRow_of_explicit_22026]
  · norm_num [dusartPrimeRow_of_explicit_22026]
  · apply DusartPrimeRowsChain.cons
    · norm_num [dusartPrimeRow_of_explicit_22026]
    · norm_num [dusartPrimeRow_of_explicit_22026]
    · apply DusartPrimeRowsChain.cons
      · norm_num [dusartPrimeRow_of_explicit_22026]
      · norm_num [dusartPrimeRow_of_explicit_22026]
      · apply DusartPrimeRowsChain.cons
        · norm_num [dusartPrimeRow_of_explicit_22026]
        · norm_num [dusartPrimeRow_of_explicit_22026]
        · apply DusartPrimeRowsChain.cons
          · norm_num [dusartPrimeRow_of_explicit_22026]
          · norm_num [dusartPrimeRow_of_explicit_22026]
          · apply DusartPrimeRowsChain.cons
            · norm_num [dusartPrimeRow_of_explicit_22026]
            · norm_num [dusartPrimeRow_of_explicit_22026]
            · apply DusartPrimeRowsChain.cons
              · norm_num [dusartPrimeRow_of_explicit_22026]
              · norm_num [dusartPrimeRow_of_explicit_22026]
              · apply DusartPrimeRowsChain.cons
                · norm_num [dusartPrimeRow_of_explicit_22026]
                · norm_num [dusartPrimeRow_of_explicit_22026]
                · apply DusartPrimeRowsChain.empty
                  norm_num
