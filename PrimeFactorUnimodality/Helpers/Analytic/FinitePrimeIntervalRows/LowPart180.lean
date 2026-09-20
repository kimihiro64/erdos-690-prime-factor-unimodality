import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowBase

set_option autoImplicit false
set_option maxRecDepth 100000

/-! # Lower finite Dusart prefix chunk 180 -/

namespace PrimeFactorUnimodality

noncomputable section
set_option maxHeartbeats 20000000 in
theorem lowPrime_15439 : Nat.Prime 15439 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 15439 15438 1 3 [2, 3, 31, 83]
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
    · change IsUnit ((3 : ZMod 15439) ^ 7719 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (7719 : ZMod 15439)
      decide
    · change IsUnit ((3 : ZMod 15439) ^ 5146 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (12940 : ZMod 15439)
      decide
    · change IsUnit ((3 : ZMod 15439) ^ 498 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (15220 : ZMod 15439)
      decide
    · change IsUnit ((3 : ZMod 15439) ^ 186 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (6490 : ZMod 15439)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_15443 : Nat.Prime 15443 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 15443 15442 1 2 [2, 7, 1103]
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
    · change IsUnit ((2 : ZMod 15443) ^ 7721 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (7721 : ZMod 15443)
      decide
    · change IsUnit ((2 : ZMod 15443) ^ 2206 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (13870 : ZMod 15443)
      decide
    · change IsUnit ((2 : ZMod 15443) ^ 14 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (15328 : ZMod 15443)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_15451 : Nat.Prime 15451 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 15451 15450 1 3 [2, 3, 5, 5, 103]
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
    · change IsUnit ((3 : ZMod 15451) ^ 7725 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (7725 : ZMod 15451)
      decide
    · change IsUnit ((3 : ZMod 15451) ^ 5150 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (9781 : ZMod 15451)
      decide
    · change IsUnit ((3 : ZMod 15451) ^ 3090 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (5130 : ZMod 15451)
      decide
    · change IsUnit ((3 : ZMod 15451) ^ 3090 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (5130 : ZMod 15451)
      decide
    · change IsUnit ((3 : ZMod 15451) ^ 150 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (15399 : ZMod 15451)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_15461 : Nat.Prime 15461 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 15461 15460 1 2 [2, 2, 5, 773]
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
    · change IsUnit ((2 : ZMod 15461) ^ 7730 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (7730 : ZMod 15461)
      decide
    · change IsUnit ((2 : ZMod 15461) ^ 7730 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (7730 : ZMod 15461)
      decide
    · change IsUnit ((2 : ZMod 15461) ^ 3092 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (68 : ZMod 15461)
      decide
    · change IsUnit ((2 : ZMod 15461) ^ 20 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (4059 : ZMod 15461)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_15467 : Nat.Prime 15467 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 15467 15466 1 5 [2, 11, 19, 37]
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
    · change IsUnit ((5 : ZMod 15467) ^ 7733 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (7733 : ZMod 15467)
      decide
    · change IsUnit ((5 : ZMod 15467) ^ 1406 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (13562 : ZMod 15467)
      decide
    · change IsUnit ((5 : ZMod 15467) ^ 814 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (5100 : ZMod 15467)
      decide
    · change IsUnit ((5 : ZMod 15467) ^ 418 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (6493 : ZMod 15467)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_15473 : Nat.Prime 15473 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 15473 15472 1 3 [2, 2, 2, 2, 967]
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
    · change IsUnit ((3 : ZMod 15473) ^ 7736 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (7736 : ZMod 15473)
      decide
    · change IsUnit ((3 : ZMod 15473) ^ 7736 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (7736 : ZMod 15473)
      decide
    · change IsUnit ((3 : ZMod 15473) ^ 7736 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (7736 : ZMod 15473)
      decide
    · change IsUnit ((3 : ZMod 15473) ^ 7736 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (7736 : ZMod 15473)
      decide
    · change IsUnit ((3 : ZMod 15473) ^ 16 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (3692 : ZMod 15473)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_15493 : Nat.Prime 15493 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 15493 15492 1 5 [2, 2, 3, 1291]
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
    · change IsUnit ((5 : ZMod 15493) ^ 7746 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (7746 : ZMod 15493)
      decide
    · change IsUnit ((5 : ZMod 15493) ^ 7746 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (7746 : ZMod 15493)
      decide
    · change IsUnit ((5 : ZMod 15493) ^ 5164 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (8053 : ZMod 15493)
      decide
    · change IsUnit ((5 : ZMod 15493) ^ 12 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (11985 : ZMod 15493)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_15497 : Nat.Prime 15497 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 15497 15496 1 3 [2, 2, 2, 13, 149]
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
    · change IsUnit ((3 : ZMod 15497) ^ 7748 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (7748 : ZMod 15497)
      decide
    · change IsUnit ((3 : ZMod 15497) ^ 7748 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (7748 : ZMod 15497)
      decide
    · change IsUnit ((3 : ZMod 15497) ^ 7748 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (7748 : ZMod 15497)
      decide
    · change IsUnit ((3 : ZMod 15497) ^ 1192 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (2505 : ZMod 15497)
      decide
    · change IsUnit ((3 : ZMod 15497) ^ 104 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (1322 : ZMod 15497)
      decide
  · norm_num
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_14767_15526_part10 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_15521 (p := 15427) (q := 15439) (by exact lowPrime_15439) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_15521 (p := 15439) (q := 15443) (by exact lowPrime_15443) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_15521 (p := 15443) (q := 15451) (by exact lowPrime_15451) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_15521 (p := 15451) (q := 15461) (by exact lowPrime_15461) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_15521 (p := 15461) (q := 15467) (by exact lowPrime_15467) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_15521 (p := 15467) (q := 15473) (by exact lowPrime_15473) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_15521 (p := 15473) (q := 15493) (by exact lowPrime_15493) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_15521 (p := 15493) (q := 15497) (by exact lowPrime_15497) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_14767_15526_part10_chain :
    DusartPrimeRowsChain 15427 15497 dusartPrimeRows_14767_15526_part10 := by
  apply DusartPrimeRowsChain.cons
  · norm_num [dusartPrimeRow_of_explicit_15521]
  · norm_num [dusartPrimeRow_of_explicit_15521]
  · apply DusartPrimeRowsChain.cons
    · norm_num [dusartPrimeRow_of_explicit_15521]
    · norm_num [dusartPrimeRow_of_explicit_15521]
    · apply DusartPrimeRowsChain.cons
      · norm_num [dusartPrimeRow_of_explicit_15521]
      · norm_num [dusartPrimeRow_of_explicit_15521]
      · apply DusartPrimeRowsChain.cons
        · norm_num [dusartPrimeRow_of_explicit_15521]
        · norm_num [dusartPrimeRow_of_explicit_15521]
        · apply DusartPrimeRowsChain.cons
          · norm_num [dusartPrimeRow_of_explicit_15521]
          · norm_num [dusartPrimeRow_of_explicit_15521]
          · apply DusartPrimeRowsChain.cons
            · norm_num [dusartPrimeRow_of_explicit_15521]
            · norm_num [dusartPrimeRow_of_explicit_15521]
            · apply DusartPrimeRowsChain.cons
              · norm_num [dusartPrimeRow_of_explicit_15521]
              · norm_num [dusartPrimeRow_of_explicit_15521]
              · apply DusartPrimeRowsChain.cons
                · norm_num [dusartPrimeRow_of_explicit_15521]
                · norm_num [dusartPrimeRow_of_explicit_15521]
                · apply DusartPrimeRowsChain.empty
                  norm_num
