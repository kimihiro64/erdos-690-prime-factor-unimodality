import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowBase

set_option autoImplicit false
set_option maxRecDepth 100000

/-! # Lower finite Dusart prefix chunk 228 -/

namespace PrimeFactorUnimodality

noncomputable section
set_option maxHeartbeats 20000000 in
theorem lowPrime_21647 : Nat.Prime 21647 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 21647 21646 1 5 [2, 79, 137]
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
    · change IsUnit ((5 : ZMod 21647) ^ 10823 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (10823 : ZMod 21647)
      decide
    · change IsUnit ((5 : ZMod 21647) ^ 274 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (9293 : ZMod 21647)
      decide
    · change IsUnit ((5 : ZMod 21647) ^ 158 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (15464 : ZMod 21647)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_21649 : Nat.Prime 21649 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 21649 21648 1 14 [2, 2, 2, 2, 3, 11, 41]
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
    · change IsUnit ((14 : ZMod 21649) ^ 10824 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (10824 : ZMod 21649)
      decide
    · change IsUnit ((14 : ZMod 21649) ^ 10824 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (10824 : ZMod 21649)
      decide
    · change IsUnit ((14 : ZMod 21649) ^ 10824 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (10824 : ZMod 21649)
      decide
    · change IsUnit ((14 : ZMod 21649) ^ 10824 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (10824 : ZMod 21649)
      decide
    · change IsUnit ((14 : ZMod 21649) ^ 7216 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (2346 : ZMod 21649)
      decide
    · change IsUnit ((14 : ZMod 21649) ^ 1968 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (20718 : ZMod 21649)
      decide
    · change IsUnit ((14 : ZMod 21649) ^ 528 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (9133 : ZMod 21649)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_21661 : Nat.Prime 21661 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 21661 21660 1 2 [2, 2, 3, 5, 19, 19]
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
    · change IsUnit ((2 : ZMod 21661) ^ 10830 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (10830 : ZMod 21661)
      decide
    · change IsUnit ((2 : ZMod 21661) ^ 10830 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (10830 : ZMod 21661)
      decide
    · change IsUnit ((2 : ZMod 21661) ^ 7220 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (19567 : ZMod 21661)
      decide
    · change IsUnit ((2 : ZMod 21661) ^ 4332 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (21184 : ZMod 21661)
      decide
    · change IsUnit ((2 : ZMod 21661) ^ 1140 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (21572 : ZMod 21661)
      decide
    · change IsUnit ((2 : ZMod 21661) ^ 1140 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (21572 : ZMod 21661)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_21673 : Nat.Prime 21673 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 21673 21672 1 10 [2, 2, 2, 3, 3, 7, 43]
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
    · change IsUnit ((10 : ZMod 21673) ^ 10836 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (10836 : ZMod 21673)
      decide
    · change IsUnit ((10 : ZMod 21673) ^ 10836 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (10836 : ZMod 21673)
      decide
    · change IsUnit ((10 : ZMod 21673) ^ 10836 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (10836 : ZMod 21673)
      decide
    · change IsUnit ((10 : ZMod 21673) ^ 7224 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (7094 : ZMod 21673)
      decide
    · change IsUnit ((10 : ZMod 21673) ^ 7224 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (7094 : ZMod 21673)
      decide
    · change IsUnit ((10 : ZMod 21673) ^ 3096 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (12047 : ZMod 21673)
      decide
    · change IsUnit ((10 : ZMod 21673) ^ 504 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (14017 : ZMod 21673)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_21683 : Nat.Prime 21683 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 21683 21682 1 2 [2, 37, 293]
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
    · change IsUnit ((2 : ZMod 21683) ^ 10841 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (10841 : ZMod 21683)
      decide
    · change IsUnit ((2 : ZMod 21683) ^ 586 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (20284 : ZMod 21683)
      decide
    · change IsUnit ((2 : ZMod 21683) ^ 74 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (14982 : ZMod 21683)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_21701 : Nat.Prime 21701 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 21701 21700 1 2 [2, 2, 5, 5, 7, 31]
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
    · change IsUnit ((2 : ZMod 21701) ^ 10850 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (10850 : ZMod 21701)
      decide
    · change IsUnit ((2 : ZMod 21701) ^ 10850 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (10850 : ZMod 21701)
      decide
    · change IsUnit ((2 : ZMod 21701) ^ 4340 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (15281 : ZMod 21701)
      decide
    · change IsUnit ((2 : ZMod 21701) ^ 4340 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (15281 : ZMod 21701)
      decide
    · change IsUnit ((2 : ZMod 21701) ^ 3100 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (10822 : ZMod 21701)
      decide
    · change IsUnit ((2 : ZMod 21701) ^ 700 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (15946 : ZMod 21701)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_21713 : Nat.Prime 21713 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 21713 21712 1 3 [2, 2, 2, 2, 23, 59]
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
    · change IsUnit ((3 : ZMod 21713) ^ 10856 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (10856 : ZMod 21713)
      decide
    · change IsUnit ((3 : ZMod 21713) ^ 10856 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (10856 : ZMod 21713)
      decide
    · change IsUnit ((3 : ZMod 21713) ^ 10856 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (10856 : ZMod 21713)
      decide
    · change IsUnit ((3 : ZMod 21713) ^ 10856 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (10856 : ZMod 21713)
      decide
    · change IsUnit ((3 : ZMod 21713) ^ 944 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (6167 : ZMod 21713)
      decide
    · change IsUnit ((3 : ZMod 21713) ^ 368 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (3827 : ZMod 21713)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_21727 : Nat.Prime 21727 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 21727 21726 1 3 [2, 3, 3, 17, 71]
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
    · change IsUnit ((3 : ZMod 21727) ^ 10863 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (10863 : ZMod 21727)
      decide
    · change IsUnit ((3 : ZMod 21727) ^ 7242 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (2485 : ZMod 21727)
      decide
    · change IsUnit ((3 : ZMod 21727) ^ 7242 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (2485 : ZMod 21727)
      decide
    · change IsUnit ((3 : ZMod 21727) ^ 1278 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (18663 : ZMod 21727)
      decide
    · change IsUnit ((3 : ZMod 21727) ^ 306 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (19845 : ZMod 21727)
      decide
  · norm_num
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_20959_22026_part10 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_22026 (p := 21617) (q := 21647) (by exact lowPrime_21647) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_22026 (p := 21647) (q := 21649) (by exact lowPrime_21649) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_22026 (p := 21649) (q := 21661) (by exact lowPrime_21661) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_22026 (p := 21661) (q := 21673) (by exact lowPrime_21673) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_22026 (p := 21673) (q := 21683) (by exact lowPrime_21683) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_22026 (p := 21683) (q := 21701) (by exact lowPrime_21701) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_22026 (p := 21701) (q := 21713) (by exact lowPrime_21713) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_22026 (p := 21713) (q := 21727) (by exact lowPrime_21727) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_20959_22026_part10_chain :
    DusartPrimeRowsChain 21617 21727 dusartPrimeRows_20959_22026_part10 := by
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
