import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowBase

set_option autoImplicit false
set_option maxRecDepth 100000

/-! # Lower finite Dusart prefix chunk 23 -/

namespace PrimeFactorUnimodality

noncomputable section
set_option maxHeartbeats 20000000 in
theorem lowPrime_4679 : Nat.Prime 4679 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 4679 4678 1 11 [2, 2339]
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
    · change IsUnit ((11 : ZMod 4679) ^ 2339 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (2339 : ZMod 4679)
      decide
    · change IsUnit ((11 : ZMod 4679) ^ 2 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (39 : ZMod 4679)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_4691 : Nat.Prime 4691 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 4691 4690 1 2 [2, 5, 7, 67]
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
    · change IsUnit ((2 : ZMod 4691) ^ 2345 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (2345 : ZMod 4691)
      decide
    · change IsUnit ((2 : ZMod 4691) ^ 938 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (4520 : ZMod 4691)
      decide
    · change IsUnit ((2 : ZMod 4691) ^ 670 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (3249 : ZMod 4691)
      decide
    · change IsUnit ((2 : ZMod 4691) ^ 70 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (2617 : ZMod 4691)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_4703 : Nat.Prime 4703 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 4703 4702 1 5 [2, 2351]
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
    · change IsUnit ((5 : ZMod 4703) ^ 2351 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (2351 : ZMod 4703)
      decide
    · change IsUnit ((5 : ZMod 4703) ^ 2 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (196 : ZMod 4703)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_4721 : Nat.Prime 4721 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 4721 4720 1 6 [2, 2, 2, 2, 5, 59]
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
    · change IsUnit ((6 : ZMod 4721) ^ 2360 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (2360 : ZMod 4721)
      decide
    · change IsUnit ((6 : ZMod 4721) ^ 2360 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (2360 : ZMod 4721)
      decide
    · change IsUnit ((6 : ZMod 4721) ^ 2360 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (2360 : ZMod 4721)
      decide
    · change IsUnit ((6 : ZMod 4721) ^ 2360 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (2360 : ZMod 4721)
      decide
    · change IsUnit ((6 : ZMod 4721) ^ 944 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (2164 : ZMod 4721)
      decide
    · change IsUnit ((6 : ZMod 4721) ^ 80 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (3655 : ZMod 4721)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_4723 : Nat.Prime 4723 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 4723 4722 1 2 [2, 3, 787]
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
    · change IsUnit ((2 : ZMod 4723) ^ 2361 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (2361 : ZMod 4723)
      decide
    · change IsUnit ((2 : ZMod 4723) ^ 1574 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (2909 : ZMod 4723)
      decide
    · change IsUnit ((2 : ZMod 4723) ^ 6 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (2399 : ZMod 4723)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_4729 : Nat.Prime 4729 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 4729 4728 1 17 [2, 2, 2, 3, 197]
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
    · change IsUnit ((17 : ZMod 4729) ^ 2364 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (2364 : ZMod 4729)
      decide
    · change IsUnit ((17 : ZMod 4729) ^ 2364 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (2364 : ZMod 4729)
      decide
    · change IsUnit ((17 : ZMod 4729) ^ 2364 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (2364 : ZMod 4729)
      decide
    · change IsUnit ((17 : ZMod 4729) ^ 1576 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (897 : ZMod 4729)
      decide
    · change IsUnit ((17 : ZMod 4729) ^ 24 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (3298 : ZMod 4729)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_4733 : Nat.Prime 4733 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 4733 4732 1 5 [2, 2, 7, 13, 13]
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
    · change IsUnit ((5 : ZMod 4733) ^ 2366 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (2366 : ZMod 4733)
      decide
    · change IsUnit ((5 : ZMod 4733) ^ 2366 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (2366 : ZMod 4733)
      decide
    · change IsUnit ((5 : ZMod 4733) ^ 676 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (2754 : ZMod 4733)
      decide
    · change IsUnit ((5 : ZMod 4733) ^ 364 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (236 : ZMod 4733)
      decide
    · change IsUnit ((5 : ZMod 4733) ^ 364 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (236 : ZMod 4733)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_4751 : Nat.Prime 4751 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 4751 4750 1 19 [2, 5, 5, 5, 19]
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
    · change IsUnit ((19 : ZMod 4751) ^ 2375 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (2375 : ZMod 4751)
      decide
    · change IsUnit ((19 : ZMod 4751) ^ 950 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (4604 : ZMod 4751)
      decide
    · change IsUnit ((19 : ZMod 4751) ^ 950 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (4604 : ZMod 4751)
      decide
    · change IsUnit ((19 : ZMod 4751) ^ 950 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (4604 : ZMod 4751)
      decide
    · change IsUnit ((19 : ZMod 4751) ^ 250 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (3701 : ZMod 4751)
      decide
  · norm_num
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_4673_4918_part01 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_4914 (p := 4673) (q := 4679) (by exact lowPrime_4679) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_4914 (p := 4679) (q := 4691) (by exact lowPrime_4691) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_4914 (p := 4691) (q := 4703) (by exact lowPrime_4703) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_4914 (p := 4703) (q := 4721) (by exact lowPrime_4721) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_4914 (p := 4721) (q := 4723) (by exact lowPrime_4723) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_4914 (p := 4723) (q := 4729) (by exact lowPrime_4729) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_4914 (p := 4729) (q := 4733) (by exact lowPrime_4733) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_4914 (p := 4733) (q := 4751) (by exact lowPrime_4751) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_4673_4918_part01_chain :
    DusartPrimeRowsChain 4673 4751 dusartPrimeRows_4673_4918_part01 := by
  apply DusartPrimeRowsChain.cons
  · norm_num [dusartPrimeRow_of_explicit_4914]
  · norm_num [dusartPrimeRow_of_explicit_4914]
  · apply DusartPrimeRowsChain.cons
    · norm_num [dusartPrimeRow_of_explicit_4914]
    · norm_num [dusartPrimeRow_of_explicit_4914]
    · apply DusartPrimeRowsChain.cons
      · norm_num [dusartPrimeRow_of_explicit_4914]
      · norm_num [dusartPrimeRow_of_explicit_4914]
      · apply DusartPrimeRowsChain.cons
        · norm_num [dusartPrimeRow_of_explicit_4914]
        · norm_num [dusartPrimeRow_of_explicit_4914]
        · apply DusartPrimeRowsChain.cons
          · norm_num [dusartPrimeRow_of_explicit_4914]
          · norm_num [dusartPrimeRow_of_explicit_4914]
          · apply DusartPrimeRowsChain.cons
            · norm_num [dusartPrimeRow_of_explicit_4914]
            · norm_num [dusartPrimeRow_of_explicit_4914]
            · apply DusartPrimeRowsChain.cons
              · norm_num [dusartPrimeRow_of_explicit_4914]
              · norm_num [dusartPrimeRow_of_explicit_4914]
              · apply DusartPrimeRowsChain.cons
                · norm_num [dusartPrimeRow_of_explicit_4914]
                · norm_num [dusartPrimeRow_of_explicit_4914]
                · apply DusartPrimeRowsChain.empty
                  norm_num
