import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowBase

set_option autoImplicit false
set_option maxRecDepth 1000000

/-! # Lower finite Dusart prefix chunk 95 -/

namespace PrimeFactorUnimodality

noncomputable section
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_9337 : Nat.Prime 9337 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 9337 9336 1 5 [2, 2, 2, 3, 389]
  · norm_num
  · norm_num
  · norm_num
  · intro p hp
    simp at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl
    all_goals decide
  · norm_num
  · norm_num
  · decide
  · intro q hq
    simp at hq
    rcases hq with rfl | rfl | rfl
    · apply IsUnit.of_mul_eq_one (4668 : ZMod 9337)
      decide
    · apply IsUnit.of_mul_eq_one (1466 : ZMod 9337)
      decide
    · apply IsUnit.of_mul_eq_one (6887 : ZMod 9337)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_9341 : Nat.Prime 9341 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 9341 9340 1 2 [2, 2, 5, 467]
  · norm_num
  · norm_num
  · norm_num
  · intro p hp
    simp at hp
    rcases hp with rfl | rfl | rfl | rfl
    all_goals decide
  · norm_num
  · norm_num
  · decide
  · intro q hq
    simp at hq
    rcases hq with rfl | rfl | rfl
    · apply IsUnit.of_mul_eq_one (4670 : ZMod 9341)
      decide
    · apply IsUnit.of_mul_eq_one (1454 : ZMod 9341)
      decide
    · apply IsUnit.of_mul_eq_one (8314 : ZMod 9341)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_9343 : Nat.Prime 9343 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 9343 9342 1 5 [2, 3, 3, 3, 173]
  · norm_num
  · norm_num
  · norm_num
  · intro p hp
    simp at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl
    all_goals decide
  · norm_num
  · norm_num
  · decide
  · intro q hq
    simp at hq
    rcases hq with rfl | rfl | rfl
    · apply IsUnit.of_mul_eq_one (4671 : ZMod 9343)
      decide
    · apply IsUnit.of_mul_eq_one (2037 : ZMod 9343)
      decide
    · apply IsUnit.of_mul_eq_one (6134 : ZMod 9343)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_9349 : Nat.Prime 9349 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 9349 9348 1 2 [2, 2, 3, 19, 41]
  · norm_num
  · norm_num
  · norm_num
  · intro p hp
    simp at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl
    all_goals decide
  · norm_num
  · norm_num
  · decide
  · intro q hq
    simp at hq
    rcases hq with rfl | rfl | rfl | rfl
    · apply IsUnit.of_mul_eq_one (4674 : ZMod 9349)
      decide
    · apply IsUnit.of_mul_eq_one (4892 : ZMod 9349)
      decide
    · apply IsUnit.of_mul_eq_one (1444 : ZMod 9349)
      decide
    · apply IsUnit.of_mul_eq_one (7422 : ZMod 9349)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_9371 : Nat.Prime 9371 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 9371 9370 1 2 [2, 5, 937]
  · norm_num
  · norm_num
  · norm_num
  · intro p hp
    simp at hp
    rcases hp with rfl | rfl | rfl
    all_goals decide
  · norm_num
  · norm_num
  · decide
  · intro q hq
    simp at hq
    rcases hq with rfl | rfl | rfl
    · apply IsUnit.of_mul_eq_one (4685 : ZMod 9371)
      decide
    · apply IsUnit.of_mul_eq_one (503 : ZMod 9371)
      decide
    · apply IsUnit.of_mul_eq_one (8171 : ZMod 9371)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_9377 : Nat.Prime 9377 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 9377 9376 1 3 [2, 2, 2, 2, 2, 293]
  · norm_num
  · norm_num
  · norm_num
  · intro p hp
    simp at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl
    all_goals decide
  · norm_num
  · norm_num
  · decide
  · intro q hq
    simp at hq
    rcases hq with rfl | rfl
    · apply IsUnit.of_mul_eq_one (4688 : ZMod 9377)
      decide
    · apply IsUnit.of_mul_eq_one (6938 : ZMod 9377)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_9391 : Nat.Prime 9391 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 9391 9390 1 3 [2, 3, 5, 313]
  · norm_num
  · norm_num
  · norm_num
  · intro p hp
    simp at hp
    rcases hp with rfl | rfl | rfl | rfl
    all_goals decide
  · norm_num
  · norm_num
  · decide
  · intro q hq
    simp at hq
    rcases hq with rfl | rfl | rfl | rfl
    · apply IsUnit.of_mul_eq_one (4695 : ZMod 9391)
      decide
    · apply IsUnit.of_mul_eq_one (2802 : ZMod 9391)
      decide
    · apply IsUnit.of_mul_eq_one (5086 : ZMod 9391)
      decide
    · apply IsUnit.of_mul_eq_one (3807 : ZMod 9391)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_9397 : Nat.Prime 9397 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 9397 9396 1 2 [2, 2, 3, 3, 3, 3, 29]
  · norm_num
  · norm_num
  · norm_num
  · intro p hp
    simp at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals decide
  · norm_num
  · norm_num
  · decide
  · intro q hq
    simp at hq
    rcases hq with rfl | rfl | rfl
    · apply IsUnit.of_mul_eq_one (4698 : ZMod 9397)
      decide
    · apply IsUnit.of_mul_eq_one (7139 : ZMod 9397)
      decide
    · apply IsUnit.of_mul_eq_one (8974 : ZMod 9397)
      decide
  · norm_num
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_8963_9418_part06 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_9414 (p := 9323) (q := 9337) (by exact lowPrime_9337) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9414 (p := 9337) (q := 9341) (by exact lowPrime_9341) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9414 (p := 9341) (q := 9343) (by exact lowPrime_9343) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9414 (p := 9343) (q := 9349) (by exact lowPrime_9349) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9414 (p := 9349) (q := 9371) (by exact lowPrime_9371) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9414 (p := 9371) (q := 9377) (by exact lowPrime_9377) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9414 (p := 9377) (q := 9391) (by exact lowPrime_9391) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9414 (p := 9391) (q := 9397) (by exact lowPrime_9397) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_8963_9418_part06_chain :
    DusartPrimeRowsChain 9323 9396 dusartPrimeRows_8963_9418_part06 := by
  apply DusartPrimeRowsChain.cons
  · norm_num [dusartPrimeRow_of_explicit_9414]
  · norm_num [dusartPrimeRow_of_explicit_9414]
  · apply DusartPrimeRowsChain.cons
    · norm_num [dusartPrimeRow_of_explicit_9414]
    · norm_num [dusartPrimeRow_of_explicit_9414]
    · apply DusartPrimeRowsChain.cons
      · norm_num [dusartPrimeRow_of_explicit_9414]
      · norm_num [dusartPrimeRow_of_explicit_9414]
      · apply DusartPrimeRowsChain.cons
        · norm_num [dusartPrimeRow_of_explicit_9414]
        · norm_num [dusartPrimeRow_of_explicit_9414]
        · apply DusartPrimeRowsChain.cons
          · norm_num [dusartPrimeRow_of_explicit_9414]
          · norm_num [dusartPrimeRow_of_explicit_9414]
          · apply DusartPrimeRowsChain.cons
            · norm_num [dusartPrimeRow_of_explicit_9414]
            · norm_num [dusartPrimeRow_of_explicit_9414]
            · apply DusartPrimeRowsChain.cons
              · norm_num [dusartPrimeRow_of_explicit_9414]
              · norm_num [dusartPrimeRow_of_explicit_9414]
              · apply DusartPrimeRowsChain.cons
                · norm_num [dusartPrimeRow_of_explicit_9414]
                · norm_num [dusartPrimeRow_of_explicit_9414]
                · apply DusartPrimeRowsChain.empty
                  norm_num [dusartPrimeRow_of_explicit_9414, dusartPrimeRow_of_explicit_right]
