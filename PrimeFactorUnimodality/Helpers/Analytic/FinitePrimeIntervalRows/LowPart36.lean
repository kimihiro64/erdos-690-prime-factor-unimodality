import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowBase

set_option autoImplicit false
set_option maxRecDepth 100000

/-! # Lower finite Dusart prefix chunk 36 -/

namespace PrimeFactorUnimodality

noncomputable section
set_option maxHeartbeats 20000000 in
theorem lowPrime_5503 : Nat.Prime 5503 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 5503 5502 1 3 [2, 3, 7, 131]
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
    · change IsUnit ((3 : ZMod 5503) ^ 2751 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (2751 : ZMod 5503)
      decide
    · change IsUnit ((3 : ZMod 5503) ^ 1834 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (3978 : ZMod 5503)
      decide
    · change IsUnit ((3 : ZMod 5503) ^ 786 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (4163 : ZMod 5503)
      decide
    · change IsUnit ((3 : ZMod 5503) ^ 42 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (2529 : ZMod 5503)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_5507 : Nat.Prime 5507 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 5507 5506 1 2 [2, 2753]
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
    · change IsUnit ((2 : ZMod 5507) ^ 2753 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (2753 : ZMod 5507)
      decide
    · change IsUnit ((2 : ZMod 5507) ^ 2 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (1836 : ZMod 5507)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_5519 : Nat.Prime 5519 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 5519 5518 1 13 [2, 31, 89]
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
    · change IsUnit ((13 : ZMod 5519) ^ 2759 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (2759 : ZMod 5519)
      decide
    · change IsUnit ((13 : ZMod 5519) ^ 178 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (2745 : ZMod 5519)
      decide
    · change IsUnit ((13 : ZMod 5519) ^ 62 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (943 : ZMod 5519)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_5521 : Nat.Prime 5521 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 5521 5520 1 11 [2, 2, 2, 2, 3, 5, 23]
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
    · change IsUnit ((11 : ZMod 5521) ^ 2760 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (2760 : ZMod 5521)
      decide
    · change IsUnit ((11 : ZMod 5521) ^ 2760 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (2760 : ZMod 5521)
      decide
    · change IsUnit ((11 : ZMod 5521) ^ 2760 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (2760 : ZMod 5521)
      decide
    · change IsUnit ((11 : ZMod 5521) ^ 2760 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (2760 : ZMod 5521)
      decide
    · change IsUnit ((11 : ZMod 5521) ^ 1840 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (113 : ZMod 5521)
      decide
    · change IsUnit ((11 : ZMod 5521) ^ 1104 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (571 : ZMod 5521)
      decide
    · change IsUnit ((11 : ZMod 5521) ^ 240 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (2270 : ZMod 5521)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_5527 : Nat.Prime 5527 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 5527 5526 1 5 [2, 3, 3, 307]
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
    · change IsUnit ((5 : ZMod 5527) ^ 2763 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (2763 : ZMod 5527)
      decide
    · change IsUnit ((5 : ZMod 5527) ^ 1842 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (3392 : ZMod 5527)
      decide
    · change IsUnit ((5 : ZMod 5527) ^ 1842 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (3392 : ZMod 5527)
      decide
    · change IsUnit ((5 : ZMod 5527) ^ 18 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (4760 : ZMod 5527)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_5531 : Nat.Prime 5531 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 5531 5530 1 10 [2, 5, 7, 79]
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
    · change IsUnit ((10 : ZMod 5531) ^ 2765 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (2765 : ZMod 5531)
      decide
    · change IsUnit ((10 : ZMod 5531) ^ 1106 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (2080 : ZMod 5531)
      decide
    · change IsUnit ((10 : ZMod 5531) ^ 790 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (2446 : ZMod 5531)
      decide
    · change IsUnit ((10 : ZMod 5531) ^ 70 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (733 : ZMod 5531)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_5557 : Nat.Prime 5557 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 5557 5556 1 2 [2, 2, 3, 463]
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
    · change IsUnit ((2 : ZMod 5557) ^ 2778 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (2778 : ZMod 5557)
      decide
    · change IsUnit ((2 : ZMod 5557) ^ 2778 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (2778 : ZMod 5557)
      decide
    · change IsUnit ((2 : ZMod 5557) ^ 1852 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (3095 : ZMod 5557)
      decide
    · change IsUnit ((2 : ZMod 5557) ^ 12 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (3972 : ZMod 5557)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_5563 : Nat.Prime 5563 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 5563 5562 1 2 [2, 3, 3, 3, 103]
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
    · change IsUnit ((2 : ZMod 5563) ^ 2781 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (2781 : ZMod 5563)
      decide
    · change IsUnit ((2 : ZMod 5563) ^ 1854 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (3471 : ZMod 5563)
      decide
    · change IsUnit ((2 : ZMod 5563) ^ 1854 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (3471 : ZMod 5563)
      decide
    · change IsUnit ((2 : ZMod 5563) ^ 1854 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (3471 : ZMod 5563)
      decide
    · change IsUnit ((2 : ZMod 5563) ^ 54 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (5473 : ZMod 5563)
      decide
  · norm_num
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_5437_5710_part02 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_5710 (p := 5501) (q := 5503) (by exact lowPrime_5503) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_5710 (p := 5503) (q := 5507) (by exact lowPrime_5507) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_5710 (p := 5507) (q := 5519) (by exact lowPrime_5519) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_5710 (p := 5519) (q := 5521) (by exact lowPrime_5521) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_5710 (p := 5521) (q := 5527) (by exact lowPrime_5527) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_5710 (p := 5527) (q := 5531) (by exact lowPrime_5531) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_5710 (p := 5531) (q := 5557) (by exact lowPrime_5557) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_5710 (p := 5557) (q := 5563) (by exact lowPrime_5563) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_5437_5710_part02_chain :
    DusartPrimeRowsChain 5501 5563 dusartPrimeRows_5437_5710_part02 := by
  apply DusartPrimeRowsChain.cons
  · norm_num [dusartPrimeRow_of_explicit_5710]
  · norm_num [dusartPrimeRow_of_explicit_5710]
  · apply DusartPrimeRowsChain.cons
    · norm_num [dusartPrimeRow_of_explicit_5710]
    · norm_num [dusartPrimeRow_of_explicit_5710]
    · apply DusartPrimeRowsChain.cons
      · norm_num [dusartPrimeRow_of_explicit_5710]
      · norm_num [dusartPrimeRow_of_explicit_5710]
      · apply DusartPrimeRowsChain.cons
        · norm_num [dusartPrimeRow_of_explicit_5710]
        · norm_num [dusartPrimeRow_of_explicit_5710]
        · apply DusartPrimeRowsChain.cons
          · norm_num [dusartPrimeRow_of_explicit_5710]
          · norm_num [dusartPrimeRow_of_explicit_5710]
          · apply DusartPrimeRowsChain.cons
            · norm_num [dusartPrimeRow_of_explicit_5710]
            · norm_num [dusartPrimeRow_of_explicit_5710]
            · apply DusartPrimeRowsChain.cons
              · norm_num [dusartPrimeRow_of_explicit_5710]
              · norm_num [dusartPrimeRow_of_explicit_5710]
              · apply DusartPrimeRowsChain.cons
                · norm_num [dusartPrimeRow_of_explicit_5710]
                · norm_num [dusartPrimeRow_of_explicit_5710]
                · apply DusartPrimeRowsChain.empty
                  norm_num
