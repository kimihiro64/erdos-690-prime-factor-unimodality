import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowBase

set_option autoImplicit false
set_option maxRecDepth 100000

/-! # Lower finite Dusart prefix chunk 97 -/

namespace PrimeFactorUnimodality

noncomputable section
set_option maxHeartbeats 20000000 in
theorem lowPrime_9421 : Nat.Prime 9421 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 9421 9420 1 2 [2, 2, 3, 5, 157]
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
    · change IsUnit ((2 : ZMod 9421) ^ 4710 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (4710 : ZMod 9421)
      decide
    · change IsUnit ((2 : ZMod 9421) ^ 4710 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (4710 : ZMod 9421)
      decide
    · change IsUnit ((2 : ZMod 9421) ^ 3140 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (5487 : ZMod 9421)
      decide
    · change IsUnit ((2 : ZMod 9421) ^ 1884 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (1422 : ZMod 9421)
      decide
    · change IsUnit ((2 : ZMod 9421) ^ 60 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (5882 : ZMod 9421)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_9431 : Nat.Prime 9431 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 9431 9430 1 7 [2, 5, 23, 41]
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
    · change IsUnit ((7 : ZMod 9431) ^ 4715 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (4715 : ZMod 9431)
      decide
    · change IsUnit ((7 : ZMod 9431) ^ 1886 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (4550 : ZMod 9431)
      decide
    · change IsUnit ((7 : ZMod 9431) ^ 410 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (7666 : ZMod 9431)
      decide
    · change IsUnit ((7 : ZMod 9431) ^ 230 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (7711 : ZMod 9431)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_9433 : Nat.Prime 9433 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 9433 9432 1 5 [2, 2, 2, 3, 3, 131]
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
    · change IsUnit ((5 : ZMod 9433) ^ 4716 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (4716 : ZMod 9433)
      decide
    · change IsUnit ((5 : ZMod 9433) ^ 4716 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (4716 : ZMod 9433)
      decide
    · change IsUnit ((5 : ZMod 9433) ^ 4716 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (4716 : ZMod 9433)
      decide
    · change IsUnit ((5 : ZMod 9433) ^ 3144 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (2835 : ZMod 9433)
      decide
    · change IsUnit ((5 : ZMod 9433) ^ 3144 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (2835 : ZMod 9433)
      decide
    · change IsUnit ((5 : ZMod 9433) ^ 72 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (6104 : ZMod 9433)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_9437 : Nat.Prime 9437 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 9437 9436 1 2 [2, 2, 7, 337]
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
    · change IsUnit ((2 : ZMod 9437) ^ 4718 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (4718 : ZMod 9437)
      decide
    · change IsUnit ((2 : ZMod 9437) ^ 4718 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (4718 : ZMod 9437)
      decide
    · change IsUnit ((2 : ZMod 9437) ^ 1348 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (5833 : ZMod 9437)
      decide
    · change IsUnit ((2 : ZMod 9437) ^ 28 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (2831 : ZMod 9437)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_9439 : Nat.Prime 9439 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 9439 9438 1 22 [2, 3, 11, 11, 13]
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
    · change IsUnit ((22 : ZMod 9439) ^ 4719 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (4719 : ZMod 9439)
      decide
    · change IsUnit ((22 : ZMod 9439) ^ 3146 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (9194 : ZMod 9439)
      decide
    · change IsUnit ((22 : ZMod 9439) ^ 858 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (4151 : ZMod 9439)
      decide
    · change IsUnit ((22 : ZMod 9439) ^ 858 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (4151 : ZMod 9439)
      decide
    · change IsUnit ((22 : ZMod 9439) ^ 726 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (1818 : ZMod 9439)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_9461 : Nat.Prime 9461 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 9461 9460 1 3 [2, 2, 5, 11, 43]
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
    · change IsUnit ((3 : ZMod 9461) ^ 4730 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (4730 : ZMod 9461)
      decide
    · change IsUnit ((3 : ZMod 9461) ^ 4730 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (4730 : ZMod 9461)
      decide
    · change IsUnit ((3 : ZMod 9461) ^ 1892 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (6536 : ZMod 9461)
      decide
    · change IsUnit ((3 : ZMod 9461) ^ 860 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (9317 : ZMod 9461)
      decide
    · change IsUnit ((3 : ZMod 9461) ^ 220 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (2783 : ZMod 9461)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_9463 : Nat.Prime 9463 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 9463 9462 1 3 [2, 3, 19, 83]
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
    · change IsUnit ((3 : ZMod 9463) ^ 4731 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (4731 : ZMod 9463)
      decide
    · change IsUnit ((3 : ZMod 9463) ^ 3154 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (9260 : ZMod 9463)
      decide
    · change IsUnit ((3 : ZMod 9463) ^ 498 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (6531 : ZMod 9463)
      decide
    · change IsUnit ((3 : ZMod 9463) ^ 114 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (6606 : ZMod 9463)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_9467 : Nat.Prime 9467 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 9467 9466 1 2 [2, 4733]
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
    · change IsUnit ((2 : ZMod 9467) ^ 4733 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (4733 : ZMod 9467)
      decide
    · change IsUnit ((2 : ZMod 9467) ^ 2 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (3156 : ZMod 9467)
      decide
  · norm_num
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_9419_9900_part01 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_9897 (p := 9419) (q := 9421) (by exact lowPrime_9421) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9897 (p := 9421) (q := 9431) (by exact lowPrime_9431) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9897 (p := 9431) (q := 9433) (by exact lowPrime_9433) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9897 (p := 9433) (q := 9437) (by exact lowPrime_9437) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9897 (p := 9437) (q := 9439) (by exact lowPrime_9439) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9897 (p := 9439) (q := 9461) (by exact lowPrime_9461) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9897 (p := 9461) (q := 9463) (by exact lowPrime_9463) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9897 (p := 9463) (q := 9467) (by exact lowPrime_9467) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_9419_9900_part01_chain :
    DusartPrimeRowsChain 9419 9467 dusartPrimeRows_9419_9900_part01 := by
  apply DusartPrimeRowsChain.cons
  · norm_num [dusartPrimeRow_of_explicit_9897]
  · norm_num [dusartPrimeRow_of_explicit_9897]
  · apply DusartPrimeRowsChain.cons
    · norm_num [dusartPrimeRow_of_explicit_9897]
    · norm_num [dusartPrimeRow_of_explicit_9897]
    · apply DusartPrimeRowsChain.cons
      · norm_num [dusartPrimeRow_of_explicit_9897]
      · norm_num [dusartPrimeRow_of_explicit_9897]
      · apply DusartPrimeRowsChain.cons
        · norm_num [dusartPrimeRow_of_explicit_9897]
        · norm_num [dusartPrimeRow_of_explicit_9897]
        · apply DusartPrimeRowsChain.cons
          · norm_num [dusartPrimeRow_of_explicit_9897]
          · norm_num [dusartPrimeRow_of_explicit_9897]
          · apply DusartPrimeRowsChain.cons
            · norm_num [dusartPrimeRow_of_explicit_9897]
            · norm_num [dusartPrimeRow_of_explicit_9897]
            · apply DusartPrimeRowsChain.cons
              · norm_num [dusartPrimeRow_of_explicit_9897]
              · norm_num [dusartPrimeRow_of_explicit_9897]
              · apply DusartPrimeRowsChain.cons
                · norm_num [dusartPrimeRow_of_explicit_9897]
                · norm_num [dusartPrimeRow_of_explicit_9897]
                · apply DusartPrimeRowsChain.empty
                  norm_num
