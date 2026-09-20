import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowBase

set_option autoImplicit false
set_option maxRecDepth 1000000

/-! # Lower finite Dusart prefix chunk 13 -/

namespace PrimeFactorUnimodality

noncomputable section
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_13249 : Nat.Prime 13249 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 13249 13248 1 7 [2, 2, 2, 2, 2, 2, 3, 3, 23]
  · norm_num
  · norm_num
  · norm_num
  · intro p hp
    simp at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals decide
  · norm_num
  · norm_num
  · decide
  · intro q hq
    simp at hq
    rcases hq with rfl | rfl | rfl
    · apply IsUnit.of_mul_eq_one (6624 : ZMod 13249)
      decide
    · apply IsUnit.of_mul_eq_one (1069 : ZMod 13249)
      decide
    · apply IsUnit.of_mul_eq_one (11912 : ZMod 13249)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_13259 : Nat.Prime 13259 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 13259 13258 1 6 [2, 7, 947]
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
    · apply IsUnit.of_mul_eq_one (6629 : ZMod 13259)
      decide
    · apply IsUnit.of_mul_eq_one (9405 : ZMod 13259)
      decide
    · apply IsUnit.of_mul_eq_one (4084 : ZMod 13259)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_13267 : Nat.Prime 13267 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 13267 13266 1 3 [2, 3, 3, 11, 67]
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
    · apply IsUnit.of_mul_eq_one (6633 : ZMod 13267)
      decide
    · apply IsUnit.of_mul_eq_one (13200 : ZMod 13267)
      decide
    · apply IsUnit.of_mul_eq_one (5898 : ZMod 13267)
      decide
    · apply IsUnit.of_mul_eq_one (12133 : ZMod 13267)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_13291 : Nat.Prime 13291 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 13291 13290 1 2 [2, 3, 5, 443]
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
    · apply IsUnit.of_mul_eq_one (6645 : ZMod 13291)
      decide
    · apply IsUnit.of_mul_eq_one (5512 : ZMod 13291)
      decide
    · apply IsUnit.of_mul_eq_one (8444 : ZMod 13291)
      decide
    · apply IsUnit.of_mul_eq_one (6881 : ZMod 13291)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_13297 : Nat.Prime 13297 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 13297 13296 1 5 [2, 2, 2, 2, 3, 277]
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
    rcases hq with rfl | rfl | rfl
    · apply IsUnit.of_mul_eq_one (6648 : ZMod 13297)
      decide
    · apply IsUnit.of_mul_eq_one (3632 : ZMod 13297)
      decide
    · apply IsUnit.of_mul_eq_one (1776 : ZMod 13297)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_13309 : Nat.Prime 13309 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 13309 13308 1 6 [2, 2, 3, 1109]
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
    · apply IsUnit.of_mul_eq_one (6654 : ZMod 13309)
      decide
    · apply IsUnit.of_mul_eq_one (7171 : ZMod 13309)
      decide
    · apply IsUnit.of_mul_eq_one (10416 : ZMod 13309)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_13313 : Nat.Prime 13313 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 13313 13312 1 3 [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 13]
  · norm_num
  · norm_num
  · norm_num
  · intro p hp
    simp at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals decide
  · norm_num
  · norm_num
  · decide
  · intro q hq
    simp at hq
    rcases hq with rfl | rfl
    · apply IsUnit.of_mul_eq_one (6656 : ZMod 13313)
      decide
    · apply IsUnit.of_mul_eq_one (11517 : ZMod 13313)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_13327 : Nat.Prime 13327 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 13327 13326 1 3 [2, 3, 2221]
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
    · apply IsUnit.of_mul_eq_one (6663 : ZMod 13327)
      decide
    · apply IsUnit.of_mul_eq_one (12279 : ZMod 13327)
      decide
    · apply IsUnit.of_mul_eq_one (11295 : ZMod 13327)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_13331 : Nat.Prime 13331 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 13331 13330 1 2 [2, 5, 31, 43]
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
    · apply IsUnit.of_mul_eq_one (6665 : ZMod 13331)
      decide
    · apply IsUnit.of_mul_eq_one (8391 : ZMod 13331)
      decide
    · apply IsUnit.of_mul_eq_one (4902 : ZMod 13331)
      decide
    · apply IsUnit.of_mul_eq_one (1349 : ZMod 13331)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_13337 : Nat.Prime 13337 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 13337 13336 1 3 [2, 2, 2, 1667]
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
    rcases hq with rfl | rfl
    · apply IsUnit.of_mul_eq_one (6668 : ZMod 13337)
      decide
    · apply IsUnit.of_mul_eq_one (12538 : ZMod 13337)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_13339 : Nat.Prime 13339 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 13339 13338 1 2 [2, 3, 3, 3, 13, 19]
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
    rcases hq with rfl | rfl | rfl | rfl
    · apply IsUnit.of_mul_eq_one (6669 : ZMod 13339)
      decide
    · apply IsUnit.of_mul_eq_one (10196 : ZMod 13339)
      decide
    · apply IsUnit.of_mul_eq_one (5147 : ZMod 13339)
      decide
    · apply IsUnit.of_mul_eq_one (2731 : ZMod 13339)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_13367 : Nat.Prime 13367 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 13367 13366 1 5 [2, 41, 163]
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
    · apply IsUnit.of_mul_eq_one (6683 : ZMod 13367)
      decide
    · apply IsUnit.of_mul_eq_one (11901 : ZMod 13367)
      decide
    · apply IsUnit.of_mul_eq_one (566 : ZMod 13367)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_13381 : Nat.Prime 13381 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 13381 13380 1 10 [2, 2, 3, 5, 223]
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
    · apply IsUnit.of_mul_eq_one (6690 : ZMod 13381)
      decide
    · apply IsUnit.of_mul_eq_one (467 : ZMod 13381)
      decide
    · apply IsUnit.of_mul_eq_one (3923 : ZMod 13381)
      decide
    · apply IsUnit.of_mul_eq_one (12699 : ZMod 13381)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_13397 : Nat.Prime 13397 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 13397 13396 1 2 [2, 2, 17, 197]
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
    · apply IsUnit.of_mul_eq_one (6698 : ZMod 13397)
      decide
    · apply IsUnit.of_mul_eq_one (7020 : ZMod 13397)
      decide
    · apply IsUnit.of_mul_eq_one (9128 : ZMod 13397)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_13399 : Nat.Prime 13399 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 13399 13398 1 3 [2, 3, 7, 11, 29]
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
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · apply IsUnit.of_mul_eq_one (6699 : ZMod 13399)
      decide
    · apply IsUnit.of_mul_eq_one (3492 : ZMod 13399)
      decide
    · apply IsUnit.of_mul_eq_one (3265 : ZMod 13399)
      decide
    · apply IsUnit.of_mul_eq_one (10715 : ZMod 13399)
      decide
    · apply IsUnit.of_mul_eq_one (377 : ZMod 13399)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_13411 : Nat.Prime 13411 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 13411 13410 1 2 [2, 3, 3, 5, 149]
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
    · apply IsUnit.of_mul_eq_one (6705 : ZMod 13411)
      decide
    · apply IsUnit.of_mul_eq_one (12752 : ZMod 13411)
      decide
    · apply IsUnit.of_mul_eq_one (950 : ZMod 13411)
      decide
    · apply IsUnit.of_mul_eq_one (7784 : ZMod 13411)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_13417 : Nat.Prime 13417 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 13417 13416 1 5 [2, 2, 2, 3, 13, 43]
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
    rcases hq with rfl | rfl | rfl | rfl
    · apply IsUnit.of_mul_eq_one (6708 : ZMod 13417)
      decide
    · apply IsUnit.of_mul_eq_one (8108 : ZMod 13417)
      decide
    · apply IsUnit.of_mul_eq_one (10793 : ZMod 13417)
      decide
    · apply IsUnit.of_mul_eq_one (7977 : ZMod 13417)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_13421 : Nat.Prime 13421 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 13421 13420 1 10 [2, 2, 5, 11, 61]
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
    · apply IsUnit.of_mul_eq_one (6710 : ZMod 13421)
      decide
    · apply IsUnit.of_mul_eq_one (2125 : ZMod 13421)
      decide
    · apply IsUnit.of_mul_eq_one (8581 : ZMod 13421)
      decide
    · apply IsUnit.of_mul_eq_one (12494 : ZMod 13421)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_13441 : Nat.Prime 13441 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 13441 13440 1 11 [2, 2, 2, 2, 2, 2, 2, 3, 5, 7]
  · norm_num
  · norm_num
  · norm_num
  · intro p hp
    simp at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals decide
  · norm_num
  · norm_num
  · decide
  · intro q hq
    simp at hq
    rcases hq with rfl | rfl | rfl | rfl
    · apply IsUnit.of_mul_eq_one (6720 : ZMod 13441)
      decide
    · apply IsUnit.of_mul_eq_one (8745 : ZMod 13441)
      decide
    · apply IsUnit.of_mul_eq_one (1156 : ZMod 13441)
      decide
    · apply IsUnit.of_mul_eq_one (1552 : ZMod 13441)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_13451 : Nat.Prime 13451 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 13451 13450 1 2 [2, 5, 5, 269]
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
    · apply IsUnit.of_mul_eq_one (6725 : ZMod 13451)
      decide
    · apply IsUnit.of_mul_eq_one (3205 : ZMod 13451)
      decide
    · apply IsUnit.of_mul_eq_one (9663 : ZMod 13451)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_13457 : Nat.Prime 13457 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 13457 13456 1 3 [2, 2, 2, 2, 29, 29]
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
    · apply IsUnit.of_mul_eq_one (6728 : ZMod 13457)
      decide
    · apply IsUnit.of_mul_eq_one (3592 : ZMod 13457)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_13463 : Nat.Prime 13463 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 13463 13462 1 5 [2, 53, 127]
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
    · apply IsUnit.of_mul_eq_one (6731 : ZMod 13463)
      decide
    · apply IsUnit.of_mul_eq_one (9892 : ZMod 13463)
      decide
    · apply IsUnit.of_mul_eq_one (2431 : ZMod 13463)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_13469 : Nat.Prime 13469 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 13469 13468 1 2 [2, 2, 7, 13, 37]
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
    · apply IsUnit.of_mul_eq_one (6734 : ZMod 13469)
      decide
    · apply IsUnit.of_mul_eq_one (11139 : ZMod 13469)
      decide
    · apply IsUnit.of_mul_eq_one (1940 : ZMod 13469)
      decide
    · apply IsUnit.of_mul_eq_one (11931 : ZMod 13469)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_13477 : Nat.Prime 13477 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 13477 13476 1 2 [2, 2, 3, 1123]
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
    · apply IsUnit.of_mul_eq_one (6738 : ZMod 13477)
      decide
    · apply IsUnit.of_mul_eq_one (3715 : ZMod 13477)
      decide
    · apply IsUnit.of_mul_eq_one (11114 : ZMod 13477)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_13487 : Nat.Prime 13487 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 13487 13486 1 5 [2, 11, 613]
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
    · apply IsUnit.of_mul_eq_one (6743 : ZMod 13487)
      decide
    · apply IsUnit.of_mul_eq_one (2090 : ZMod 13487)
      decide
    · apply IsUnit.of_mul_eq_one (5074 : ZMod 13487)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_13499 : Nat.Prime 13499 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 13499 13498 1 6 [2, 17, 397]
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
    · apply IsUnit.of_mul_eq_one (6749 : ZMod 13499)
      decide
    · apply IsUnit.of_mul_eq_one (9088 : ZMod 13499)
      decide
    · apply IsUnit.of_mul_eq_one (10134 : ZMod 13499)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_13513 : Nat.Prime 13513 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 13513 13512 1 5 [2, 2, 2, 3, 563]
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
    · apply IsUnit.of_mul_eq_one (6756 : ZMod 13513)
      decide
    · apply IsUnit.of_mul_eq_one (6369 : ZMod 13513)
      decide
    · apply IsUnit.of_mul_eq_one (3665 : ZMod 13513)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_13523 : Nat.Prime 13523 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 13523 13522 1 2 [2, 6761]
  · norm_num
  · norm_num
  · norm_num
  · intro p hp
    simp at hp
    rcases hp with rfl | rfl
    all_goals decide
  · norm_num
  · norm_num
  · decide
  · intro q hq
    simp at hq
    rcases hq with rfl | rfl
    · apply IsUnit.of_mul_eq_one (6761 : ZMod 13523)
      decide
    · apply IsUnit.of_mul_eq_one (4508 : ZMod 13523)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_13537 : Nat.Prime 13537 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 13537 13536 1 7 [2, 2, 2, 2, 2, 3, 3, 47]
  · norm_num
  · norm_num
  · norm_num
  · intro p hp
    simp at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals decide
  · norm_num
  · norm_num
  · decide
  · intro q hq
    simp at hq
    rcases hq with rfl | rfl | rfl
    · apply IsUnit.of_mul_eq_one (6768 : ZMod 13537)
      decide
    · apply IsUnit.of_mul_eq_one (4372 : ZMod 13537)
      decide
    · apply IsUnit.of_mul_eq_one (10420 : ZMod 13537)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_13553 : Nat.Prime 13553 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 13553 13552 1 3 [2, 2, 2, 2, 7, 11, 11]
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
    · apply IsUnit.of_mul_eq_one (6776 : ZMod 13553)
      decide
    · apply IsUnit.of_mul_eq_one (13202 : ZMod 13553)
      decide
    · apply IsUnit.of_mul_eq_one (7638 : ZMod 13553)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_13567 : Nat.Prime 13567 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 13567 13566 1 3 [2, 3, 7, 17, 19]
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
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · apply IsUnit.of_mul_eq_one (6783 : ZMod 13567)
      decide
    · apply IsUnit.of_mul_eq_one (6108 : ZMod 13567)
      decide
    · apply IsUnit.of_mul_eq_one (11095 : ZMod 13567)
      decide
    · apply IsUnit.of_mul_eq_one (11924 : ZMod 13567)
      decide
    · apply IsUnit.of_mul_eq_one (1212 : ZMod 13567)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_13577 : Nat.Prime 13577 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 13577 13576 1 3 [2, 2, 2, 1697]
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
    rcases hq with rfl | rfl
    · apply IsUnit.of_mul_eq_one (6788 : ZMod 13577)
      decide
    · apply IsUnit.of_mul_eq_one (7962 : ZMod 13577)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_13591 : Nat.Prime 13591 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 13591 13590 1 3 [2, 3, 3, 5, 151]
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
    · apply IsUnit.of_mul_eq_one (6795 : ZMod 13591)
      decide
    · apply IsUnit.of_mul_eq_one (3616 : ZMod 13591)
      decide
    · apply IsUnit.of_mul_eq_one (5994 : ZMod 13591)
      decide
    · apply IsUnit.of_mul_eq_one (3859 : ZMod 13591)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_13597 : Nat.Prime 13597 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 13597 13596 1 5 [2, 2, 3, 11, 103]
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
    · apply IsUnit.of_mul_eq_one (6798 : ZMod 13597)
      decide
    · apply IsUnit.of_mul_eq_one (12120 : ZMod 13597)
      decide
    · apply IsUnit.of_mul_eq_one (3813 : ZMod 13597)
      decide
    · apply IsUnit.of_mul_eq_one (5587 : ZMod 13597)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_13613 : Nat.Prime 13613 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 13613 13612 1 2 [2, 2, 41, 83]
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
    · apply IsUnit.of_mul_eq_one (6806 : ZMod 13613)
      decide
    · apply IsUnit.of_mul_eq_one (983 : ZMod 13613)
      decide
    · apply IsUnit.of_mul_eq_one (10062 : ZMod 13613)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_13619 : Nat.Prime 13619 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 13619 13618 1 2 [2, 11, 619]
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
    · apply IsUnit.of_mul_eq_one (6809 : ZMod 13619)
      decide
    · apply IsUnit.of_mul_eq_one (10229 : ZMod 13619)
      decide
    · apply IsUnit.of_mul_eq_one (5112 : ZMod 13619)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_13627 : Nat.Prime 13627 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 13627 13626 1 2 [2, 3, 3, 757]
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
    · apply IsUnit.of_mul_eq_one (6813 : ZMod 13627)
      decide
    · apply IsUnit.of_mul_eq_one (3467 : ZMod 13627)
      decide
    · apply IsUnit.of_mul_eq_one (12644 : ZMod 13627)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_13633 : Nat.Prime 13633 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 13633 13632 1 5 [2, 2, 2, 2, 2, 2, 3, 71]
  · norm_num
  · norm_num
  · norm_num
  · intro p hp
    simp at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals decide
  · norm_num
  · norm_num
  · decide
  · intro q hq
    simp at hq
    rcases hq with rfl | rfl | rfl
    · apply IsUnit.of_mul_eq_one (6816 : ZMod 13633)
      decide
    · apply IsUnit.of_mul_eq_one (5558 : ZMod 13633)
      decide
    · apply IsUnit.of_mul_eq_one (6864 : ZMod 13633)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_13649 : Nat.Prime 13649 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 13649 13648 1 3 [2, 2, 2, 2, 853]
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
    rcases hq with rfl | rfl
    · apply IsUnit.of_mul_eq_one (6824 : ZMod 13649)
      decide
    · apply IsUnit.of_mul_eq_one (10295 : ZMod 13649)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_13669 : Nat.Prime 13669 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 13669 13668 1 6 [2, 2, 3, 17, 67]
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
    · apply IsUnit.of_mul_eq_one (6834 : ZMod 13669)
      decide
    · apply IsUnit.of_mul_eq_one (13601 : ZMod 13669)
      decide
    · apply IsUnit.of_mul_eq_one (13158 : ZMod 13669)
      decide
    · apply IsUnit.of_mul_eq_one (8361 : ZMod 13669)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_13679 : Nat.Prime 13679 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 13679 13678 1 7 [2, 7, 977]
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
    · apply IsUnit.of_mul_eq_one (6839 : ZMod 13679)
      decide
    · apply IsUnit.of_mul_eq_one (9533 : ZMod 13679)
      decide
    · apply IsUnit.of_mul_eq_one (13325 : ZMod 13679)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_13681 : Nat.Prime 13681 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 13681 13680 1 22 [2, 2, 2, 2, 3, 3, 5, 19]
  · norm_num
  · norm_num
  · norm_num
  · intro p hp
    simp at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals decide
  · norm_num
  · norm_num
  · decide
  · intro q hq
    simp at hq
    rcases hq with rfl | rfl | rfl | rfl
    · apply IsUnit.of_mul_eq_one (6840 : ZMod 13681)
      decide
    · apply IsUnit.of_mul_eq_one (3918 : ZMod 13681)
      decide
    · apply IsUnit.of_mul_eq_one (7899 : ZMod 13681)
      decide
    · apply IsUnit.of_mul_eq_one (9620 : ZMod 13681)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_13687 : Nat.Prime 13687 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 13687 13686 1 3 [2, 3, 2281]
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
    · apply IsUnit.of_mul_eq_one (6843 : ZMod 13687)
      decide
    · apply IsUnit.of_mul_eq_one (3670 : ZMod 13687)
      decide
    · apply IsUnit.of_mul_eq_one (4531 : ZMod 13687)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_13691 : Nat.Prime 13691 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 13691 13690 1 2 [2, 5, 37, 37]
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
    · apply IsUnit.of_mul_eq_one (6845 : ZMod 13691)
      decide
    · apply IsUnit.of_mul_eq_one (12768 : ZMod 13691)
      decide
    · apply IsUnit.of_mul_eq_one (1626 : ZMod 13691)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_13693 : Nat.Prime 13693 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 13693 13692 1 6 [2, 2, 3, 7, 163]
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
    · apply IsUnit.of_mul_eq_one (6846 : ZMod 13693)
      decide
    · apply IsUnit.of_mul_eq_one (3561 : ZMod 13693)
      decide
    · apply IsUnit.of_mul_eq_one (12349 : ZMod 13693)
      decide
    · apply IsUnit.of_mul_eq_one (5523 : ZMod 13693)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_13697 : Nat.Prime 13697 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 13697 13696 1 3 [2, 2, 2, 2, 2, 2, 2, 107]
  · norm_num
  · norm_num
  · norm_num
  · intro p hp
    simp at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals decide
  · norm_num
  · norm_num
  · decide
  · intro q hq
    simp at hq
    rcases hq with rfl | rfl
    · apply IsUnit.of_mul_eq_one (6848 : ZMod 13697)
      decide
    · apply IsUnit.of_mul_eq_one (1923 : ZMod 13697)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_13709 : Nat.Prime 13709 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 13709 13708 1 2 [2, 2, 23, 149]
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
    · apply IsUnit.of_mul_eq_one (6854 : ZMod 13709)
      decide
    · apply IsUnit.of_mul_eq_one (11514 : ZMod 13709)
      decide
    · apply IsUnit.of_mul_eq_one (9931 : ZMod 13709)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_13711 : Nat.Prime 13711 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 13711 13710 1 6 [2, 3, 5, 457]
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
    · apply IsUnit.of_mul_eq_one (6855 : ZMod 13711)
      decide
    · apply IsUnit.of_mul_eq_one (1049 : ZMod 13711)
      decide
    · apply IsUnit.of_mul_eq_one (2811 : ZMod 13711)
      decide
    · apply IsUnit.of_mul_eq_one (597 : ZMod 13711)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_13721 : Nat.Prime 13721 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 13721 13720 1 3 [2, 2, 2, 5, 7, 7, 7]
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
    · apply IsUnit.of_mul_eq_one (6860 : ZMod 13721)
      decide
    · apply IsUnit.of_mul_eq_one (10624 : ZMod 13721)
      decide
    · apply IsUnit.of_mul_eq_one (5353 : ZMod 13721)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_13723 : Nat.Prime 13723 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 13723 13722 1 2 [2, 3, 2287]
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
    · apply IsUnit.of_mul_eq_one (6861 : ZMod 13723)
      decide
    · apply IsUnit.of_mul_eq_one (3857 : ZMod 13723)
      decide
    · apply IsUnit.of_mul_eq_one (5010 : ZMod 13723)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_13729 : Nat.Prime 13729 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 13729 13728 1 23 [2, 2, 2, 2, 2, 3, 11, 13]
  · norm_num
  · norm_num
  · norm_num
  · intro p hp
    simp at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals decide
  · norm_num
  · norm_num
  · decide
  · intro q hq
    simp at hq
    rcases hq with rfl | rfl | rfl | rfl
    · apply IsUnit.of_mul_eq_one (6864 : ZMod 13729)
      decide
    · apply IsUnit.of_mul_eq_one (2236 : ZMod 13729)
      decide
    · apply IsUnit.of_mul_eq_one (12927 : ZMod 13729)
      decide
    · apply IsUnit.of_mul_eq_one (294 : ZMod 13729)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_13751 : Nat.Prime 13751 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 13751 13750 1 11 [2, 5, 5, 5, 5, 11]
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
    rcases hq with rfl | rfl | rfl
    · apply IsUnit.of_mul_eq_one (6875 : ZMod 13751)
      decide
    · apply IsUnit.of_mul_eq_one (1728 : ZMod 13751)
      decide
    · apply IsUnit.of_mul_eq_one (5381 : ZMod 13751)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_13757 : Nat.Prime 13757 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 13757 13756 1 2 [2, 2, 19, 181]
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
    · apply IsUnit.of_mul_eq_one (6878 : ZMod 13757)
      decide
    · apply IsUnit.of_mul_eq_one (9457 : ZMod 13757)
      decide
    · apply IsUnit.of_mul_eq_one (10755 : ZMod 13757)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_13759 : Nat.Prime 13759 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 13759 13758 1 6 [2, 3, 2293]
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
    · apply IsUnit.of_mul_eq_one (6879 : ZMod 13759)
      decide
    · apply IsUnit.of_mul_eq_one (4348 : ZMod 13759)
      decide
    · apply IsUnit.of_mul_eq_one (1205 : ZMod 13759)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_13763 : Nat.Prime 13763 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 13763 13762 1 2 [2, 7, 983]
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
    · apply IsUnit.of_mul_eq_one (6881 : ZMod 13763)
      decide
    · apply IsUnit.of_mul_eq_one (5661 : ZMod 13763)
      decide
    · apply IsUnit.of_mul_eq_one (3010 : ZMod 13763)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_13781 : Nat.Prime 13781 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 13781 13780 1 7 [2, 2, 5, 13, 53]
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
    · apply IsUnit.of_mul_eq_one (6890 : ZMod 13781)
      decide
    · apply IsUnit.of_mul_eq_one (12442 : ZMod 13781)
      decide
    · apply IsUnit.of_mul_eq_one (5898 : ZMod 13781)
      decide
    · apply IsUnit.of_mul_eq_one (12205 : ZMod 13781)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_13789 : Nat.Prime 13789 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 13789 13788 1 7 [2, 2, 3, 3, 383]
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
    · apply IsUnit.of_mul_eq_one (6894 : ZMod 13789)
      decide
    · apply IsUnit.of_mul_eq_one (10001 : ZMod 13789)
      decide
    · apply IsUnit.of_mul_eq_one (3274 : ZMod 13789)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_13799 : Nat.Prime 13799 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 13799 13798 1 7 [2, 6899]
  · norm_num
  · norm_num
  · norm_num
  · intro p hp
    simp at hp
    rcases hp with rfl | rfl
    all_goals decide
  · norm_num
  · norm_num
  · decide
  · intro q hq
    simp at hq
    rcases hq with rfl | rfl
    · apply IsUnit.of_mul_eq_one (6899 : ZMod 13799)
      decide
    · apply IsUnit.of_mul_eq_one (7187 : ZMod 13799)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_13807 : Nat.Prime 13807 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 13807 13806 1 5 [2, 3, 3, 13, 59]
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
    · apply IsUnit.of_mul_eq_one (6903 : ZMod 13807)
      decide
    · apply IsUnit.of_mul_eq_one (9165 : ZMod 13807)
      decide
    · apply IsUnit.of_mul_eq_one (717 : ZMod 13807)
      decide
    · apply IsUnit.of_mul_eq_one (519 : ZMod 13807)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_13829 : Nat.Prime 13829 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 13829 13828 1 2 [2, 2, 3457]
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
    rcases hq with rfl | rfl
    · apply IsUnit.of_mul_eq_one (6914 : ZMod 13829)
      decide
    · apply IsUnit.of_mul_eq_one (922 : ZMod 13829)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_13831 : Nat.Prime 13831 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 13831 13830 1 6 [2, 3, 5, 461]
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
    · apply IsUnit.of_mul_eq_one (6915 : ZMod 13831)
      decide
    · apply IsUnit.of_mul_eq_one (3865 : ZMod 13831)
      decide
    · apply IsUnit.of_mul_eq_one (6077 : ZMod 13831)
      decide
    · apply IsUnit.of_mul_eq_one (6886 : ZMod 13831)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_13841 : Nat.Prime 13841 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 13841 13840 1 6 [2, 2, 2, 2, 5, 173]
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
    rcases hq with rfl | rfl | rfl
    · apply IsUnit.of_mul_eq_one (6920 : ZMod 13841)
      decide
    · apply IsUnit.of_mul_eq_one (9806 : ZMod 13841)
      decide
    · apply IsUnit.of_mul_eq_one (11066 : ZMod 13841)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_13859 : Nat.Prime 13859 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 13859 13858 1 2 [2, 13, 13, 41]
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
    · apply IsUnit.of_mul_eq_one (6929 : ZMod 13859)
      decide
    · apply IsUnit.of_mul_eq_one (5554 : ZMod 13859)
      decide
    · apply IsUnit.of_mul_eq_one (4087 : ZMod 13859)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_13873 : Nat.Prime 13873 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 13873 13872 1 5 [2, 2, 2, 2, 3, 17, 17]
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
    · apply IsUnit.of_mul_eq_one (6936 : ZMod 13873)
      decide
    · apply IsUnit.of_mul_eq_one (6970 : ZMod 13873)
      decide
    · apply IsUnit.of_mul_eq_one (4982 : ZMod 13873)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_13877 : Nat.Prime 13877 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 13877 13876 1 2 [2, 2, 3469]
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
    rcases hq with rfl | rfl
    · apply IsUnit.of_mul_eq_one (6938 : ZMod 13877)
      decide
    · apply IsUnit.of_mul_eq_one (6476 : ZMod 13877)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_13879 : Nat.Prime 13879 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 13879 13878 1 6 [2, 3, 3, 3, 257]
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
    · apply IsUnit.of_mul_eq_one (6939 : ZMod 13879)
      decide
    · apply IsUnit.of_mul_eq_one (12919 : ZMod 13879)
      decide
    · apply IsUnit.of_mul_eq_one (8004 : ZMod 13879)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_13883 : Nat.Prime 13883 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 13883 13882 1 2 [2, 11, 631]
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
    · apply IsUnit.of_mul_eq_one (6941 : ZMod 13883)
      decide
    · apply IsUnit.of_mul_eq_one (12425 : ZMod 13883)
      decide
    · apply IsUnit.of_mul_eq_one (441 : ZMod 13883)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_13901 : Nat.Prime 13901 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 13901 13900 1 2 [2, 2, 5, 5, 139]
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
    · apply IsUnit.of_mul_eq_one (6950 : ZMod 13901)
      decide
    · apply IsUnit.of_mul_eq_one (7565 : ZMod 13901)
      decide
    · apply IsUnit.of_mul_eq_one (436 : ZMod 13901)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_13903 : Nat.Prime 13903 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 13903 13902 1 3 [2, 3, 7, 331]
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
    · apply IsUnit.of_mul_eq_one (6951 : ZMod 13903)
      decide
    · apply IsUnit.of_mul_eq_one (4415 : ZMod 13903)
      decide
    · apply IsUnit.of_mul_eq_one (8438 : ZMod 13903)
      decide
    · apply IsUnit.of_mul_eq_one (3786 : ZMod 13903)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_13907 : Nat.Prime 13907 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 13907 13906 1 2 [2, 17, 409]
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
    · apply IsUnit.of_mul_eq_one (6953 : ZMod 13907)
      decide
    · apply IsUnit.of_mul_eq_one (563 : ZMod 13907)
      decide
    · apply IsUnit.of_mul_eq_one (13516 : ZMod 13907)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_13913 : Nat.Prime 13913 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 13913 13912 1 3 [2, 2, 2, 37, 47]
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
    · apply IsUnit.of_mul_eq_one (6956 : ZMod 13913)
      decide
    · apply IsUnit.of_mul_eq_one (13008 : ZMod 13913)
      decide
    · apply IsUnit.of_mul_eq_one (9566 : ZMod 13913)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_13921 : Nat.Prime 13921 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 13921 13920 1 7 [2, 2, 2, 2, 2, 3, 5, 29]
  · norm_num
  · norm_num
  · norm_num
  · intro p hp
    simp at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals decide
  · norm_num
  · norm_num
  · decide
  · intro q hq
    simp at hq
    rcases hq with rfl | rfl | rfl | rfl
    · apply IsUnit.of_mul_eq_one (6960 : ZMod 13921)
      decide
    · apply IsUnit.of_mul_eq_one (12931 : ZMod 13921)
      decide
    · apply IsUnit.of_mul_eq_one (6717 : ZMod 13921)
      decide
    · apply IsUnit.of_mul_eq_one (648 : ZMod 13921)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_13931 : Nat.Prime 13931 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 13931 13930 1 2 [2, 5, 7, 199]
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
    · apply IsUnit.of_mul_eq_one (6965 : ZMod 13931)
      decide
    · apply IsUnit.of_mul_eq_one (6123 : ZMod 13931)
      decide
    · apply IsUnit.of_mul_eq_one (4477 : ZMod 13931)
      decide
    · apply IsUnit.of_mul_eq_one (8941 : ZMod 13931)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_13933 : Nat.Prime 13933 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 13933 13932 1 2 [2, 2, 3, 3, 3, 3, 43]
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
    · apply IsUnit.of_mul_eq_one (6966 : ZMod 13933)
      decide
    · apply IsUnit.of_mul_eq_one (711 : ZMod 13933)
      decide
    · apply IsUnit.of_mul_eq_one (5120 : ZMod 13933)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_13963 : Nat.Prime 13963 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 13963 13962 1 3 [2, 3, 13, 179]
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
    · apply IsUnit.of_mul_eq_one (6981 : ZMod 13963)
      decide
    · apply IsUnit.of_mul_eq_one (180 : ZMod 13963)
      decide
    · apply IsUnit.of_mul_eq_one (1535 : ZMod 13963)
      decide
    · apply IsUnit.of_mul_eq_one (10323 : ZMod 13963)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_13967 : Nat.Prime 13967 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 13967 13966 1 5 [2, 6983]
  · norm_num
  · norm_num
  · norm_num
  · intro p hp
    simp at hp
    rcases hp with rfl | rfl
    all_goals decide
  · norm_num
  · norm_num
  · decide
  · intro q hq
    simp at hq
    rcases hq with rfl | rfl
    · apply IsUnit.of_mul_eq_one (6983 : ZMod 13967)
      decide
    · apply IsUnit.of_mul_eq_one (582 : ZMod 13967)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_13997 : Nat.Prime 13997 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 13997 13996 1 2 [2, 2, 3499]
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
    rcases hq with rfl | rfl
    · apply IsUnit.of_mul_eq_one (6998 : ZMod 13997)
      decide
    · apply IsUnit.of_mul_eq_one (6532 : ZMod 13997)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_13999 : Nat.Prime 13999 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 13999 13998 1 3 [2, 3, 2333]
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
    · apply IsUnit.of_mul_eq_one (6999 : ZMod 13999)
      decide
    · apply IsUnit.of_mul_eq_one (10736 : ZMod 13999)
      decide
    · apply IsUnit.of_mul_eq_one (8634 : ZMod 13999)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_14009 : Nat.Prime 14009 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 14009 14008 1 3 [2, 2, 2, 17, 103]
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
    · apply IsUnit.of_mul_eq_one (7004 : ZMod 14009)
      decide
    · apply IsUnit.of_mul_eq_one (10252 : ZMod 14009)
      decide
    · apply IsUnit.of_mul_eq_one (8325 : ZMod 14009)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_14011 : Nat.Prime 14011 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 14011 14010 1 2 [2, 3, 5, 467]
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
    · apply IsUnit.of_mul_eq_one (7005 : ZMod 14011)
      decide
    · apply IsUnit.of_mul_eq_one (13630 : ZMod 14011)
      decide
    · apply IsUnit.of_mul_eq_one (7782 : ZMod 14011)
      decide
    · apply IsUnit.of_mul_eq_one (13277 : ZMod 14011)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_14029 : Nat.Prime 14029 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 14029 14028 1 6 [2, 2, 3, 7, 167]
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
    · apply IsUnit.of_mul_eq_one (7014 : ZMod 14029)
      decide
    · apply IsUnit.of_mul_eq_one (11088 : ZMod 14029)
      decide
    · apply IsUnit.of_mul_eq_one (12344 : ZMod 14029)
      decide
    · apply IsUnit.of_mul_eq_one (3017 : ZMod 14029)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_14033 : Nat.Prime 14033 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 14033 14032 1 3 [2, 2, 2, 2, 877]
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
    rcases hq with rfl | rfl
    · apply IsUnit.of_mul_eq_one (7016 : ZMod 14033)
      decide
    · apply IsUnit.of_mul_eq_one (7565 : ZMod 14033)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_14051 : Nat.Prime 14051 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 14051 14050 1 2 [2, 5, 5, 281]
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
    · apply IsUnit.of_mul_eq_one (7025 : ZMod 14051)
      decide
    · apply IsUnit.of_mul_eq_one (10400 : ZMod 14051)
      decide
    · apply IsUnit.of_mul_eq_one (2225 : ZMod 14051)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_14057 : Nat.Prime 14057 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 14057 14056 1 3 [2, 2, 2, 7, 251]
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
    · apply IsUnit.of_mul_eq_one (7028 : ZMod 14057)
      decide
    · apply IsUnit.of_mul_eq_one (7520 : ZMod 14057)
      decide
    · apply IsUnit.of_mul_eq_one (12163 : ZMod 14057)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_14071 : Nat.Prime 14071 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 14071 14070 1 7 [2, 3, 5, 7, 67]
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
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · apply IsUnit.of_mul_eq_one (7035 : ZMod 14071)
      decide
    · apply IsUnit.of_mul_eq_one (9718 : ZMod 14071)
      decide
    · apply IsUnit.of_mul_eq_one (1196 : ZMod 14071)
      decide
    · apply IsUnit.of_mul_eq_one (10307 : ZMod 14071)
      decide
    · apply IsUnit.of_mul_eq_one (8635 : ZMod 14071)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_14081 : Nat.Prime 14081 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 14081 14080 1 3 [2, 2, 2, 2, 2, 2, 2, 2, 5, 11]
  · norm_num
  · norm_num
  · norm_num
  · intro p hp
    simp at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals decide
  · norm_num
  · norm_num
  · decide
  · intro q hq
    simp at hq
    rcases hq with rfl | rfl | rfl
    · apply IsUnit.of_mul_eq_one (7040 : ZMod 14081)
      decide
    · apply IsUnit.of_mul_eq_one (9826 : ZMod 14081)
      decide
    · apply IsUnit.of_mul_eq_one (5154 : ZMod 14081)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_14083 : Nat.Prime 14083 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 14083 14082 1 3 [2, 3, 2347]
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
    · apply IsUnit.of_mul_eq_one (7041 : ZMod 14083)
      decide
    · apply IsUnit.of_mul_eq_one (8463 : ZMod 14083)
      decide
    · apply IsUnit.of_mul_eq_one (561 : ZMod 14083)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_14087 : Nat.Prime 14087 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 14087 14086 1 5 [2, 7043]
  · norm_num
  · norm_num
  · norm_num
  · intro p hp
    simp at hp
    rcases hp with rfl | rfl
    all_goals decide
  · norm_num
  · norm_num
  · decide
  · intro q hq
    simp at hq
    rcases hq with rfl | rfl
    · apply IsUnit.of_mul_eq_one (7043 : ZMod 14087)
      decide
    · apply IsUnit.of_mul_eq_one (587 : ZMod 14087)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_14107 : Nat.Prime 14107 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 14107 14106 1 2 [2, 3, 2351]
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
    · apply IsUnit.of_mul_eq_one (7053 : ZMod 14107)
      decide
    · apply IsUnit.of_mul_eq_one (6418 : ZMod 14107)
      decide
    · apply IsUnit.of_mul_eq_one (8509 : ZMod 14107)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_14143 : Nat.Prime 14143 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 14143 14142 1 3 [2, 3, 2357]
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
    · apply IsUnit.of_mul_eq_one (7071 : ZMod 14143)
      decide
    · apply IsUnit.of_mul_eq_one (2990 : ZMod 14143)
      decide
    · apply IsUnit.of_mul_eq_one (12142 : ZMod 14143)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_14149 : Nat.Prime 14149 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 14149 14148 1 6 [2, 2, 3, 3, 3, 131]
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
    rcases hq with rfl | rfl | rfl
    · apply IsUnit.of_mul_eq_one (7074 : ZMod 14149)
      decide
    · apply IsUnit.of_mul_eq_one (9983 : ZMod 14149)
      decide
    · apply IsUnit.of_mul_eq_one (1348 : ZMod 14149)
      decide
  · norm_num
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_12713_13366_part08 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_13359 (p := 13241) (q := 13249) (by exact lowPrime_13249) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_13359 (p := 13249) (q := 13259) (by exact lowPrime_13259) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_13359 (p := 13259) (q := 13267) (by exact lowPrime_13267) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_13359 (p := 13267) (q := 13291) (by exact lowPrime_13291) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_13359 (p := 13291) (q := 13297) (by exact lowPrime_13297) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_13359 (p := 13297) (q := 13309) (by exact lowPrime_13309) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_13359 (p := 13309) (q := 13313) (by exact lowPrime_13313) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_13359 (p := 13313) (q := 13327) (by exact lowPrime_13327) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_12713_13366_part08_chain :
    DusartPrimeRowsChain 13241 13326 dusartPrimeRows_12713_13366_part08 := by
  apply DusartPrimeRowsChain.cons
  · norm_num [dusartPrimeRow_of_explicit_13359]
  · norm_num [dusartPrimeRow_of_explicit_13359]
  · apply DusartPrimeRowsChain.cons
    · norm_num [dusartPrimeRow_of_explicit_13359]
    · norm_num [dusartPrimeRow_of_explicit_13359]
    · apply DusartPrimeRowsChain.cons
      · norm_num [dusartPrimeRow_of_explicit_13359]
      · norm_num [dusartPrimeRow_of_explicit_13359]
      · apply DusartPrimeRowsChain.cons
        · norm_num [dusartPrimeRow_of_explicit_13359]
        · norm_num [dusartPrimeRow_of_explicit_13359]
        · apply DusartPrimeRowsChain.cons
          · norm_num [dusartPrimeRow_of_explicit_13359]
          · norm_num [dusartPrimeRow_of_explicit_13359]
          · apply DusartPrimeRowsChain.cons
            · norm_num [dusartPrimeRow_of_explicit_13359]
            · norm_num [dusartPrimeRow_of_explicit_13359]
            · apply DusartPrimeRowsChain.cons
              · norm_num [dusartPrimeRow_of_explicit_13359]
              · norm_num [dusartPrimeRow_of_explicit_13359]
              · apply DusartPrimeRowsChain.cons
                · norm_num [dusartPrimeRow_of_explicit_13359]
                · norm_num [dusartPrimeRow_of_explicit_13359]
                · apply DusartPrimeRowsChain.empty
                  norm_num [dusartPrimeRow_of_explicit_13359, dusartPrimeRow_of_explicit_right]

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_12713_13366_part09 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_13359 (p := 13327) (q := 13331) (by exact lowPrime_13331) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_13359 (p := 13331) (q := 13337) (by exact lowPrime_13337) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_13359 (p := 13337) (q := 13339) (by exact lowPrime_13339) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_13359 (p := 13339) (q := 13367) (by exact lowPrime_13367) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_12713_13366_part09_chain :
    DusartPrimeRowsChain 13327 13366 dusartPrimeRows_12713_13366_part09 := by
  apply DusartPrimeRowsChain.cons
  · norm_num [dusartPrimeRow_of_explicit_13359]
  · norm_num [dusartPrimeRow_of_explicit_13359]
  · apply DusartPrimeRowsChain.cons
    · norm_num [dusartPrimeRow_of_explicit_13359]
    · norm_num [dusartPrimeRow_of_explicit_13359]
    · apply DusartPrimeRowsChain.cons
      · norm_num [dusartPrimeRow_of_explicit_13359]
      · norm_num [dusartPrimeRow_of_explicit_13359]
      · apply DusartPrimeRowsChain.cons
        · norm_num [dusartPrimeRow_of_explicit_13359]
        · norm_num [dusartPrimeRow_of_explicit_13359]
        · apply DusartPrimeRowsChain.empty
          norm_num [dusartPrimeRow_of_explicit_13359, dusartPrimeRow_of_explicit_right]

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_13367_14050_part01 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_14044 (p := 13367) (q := 13381) (by exact lowPrime_13381) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14044 (p := 13381) (q := 13397) (by exact lowPrime_13397) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14044 (p := 13397) (q := 13399) (by exact lowPrime_13399) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14044 (p := 13399) (q := 13411) (by exact lowPrime_13411) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14044 (p := 13411) (q := 13417) (by exact lowPrime_13417) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14044 (p := 13417) (q := 13421) (by exact lowPrime_13421) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14044 (p := 13421) (q := 13441) (by exact lowPrime_13441) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14044 (p := 13441) (q := 13451) (by exact lowPrime_13451) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_13367_14050_part01_chain :
    DusartPrimeRowsChain 13367 13450 dusartPrimeRows_13367_14050_part01 := by
  apply DusartPrimeRowsChain.cons
  · norm_num [dusartPrimeRow_of_explicit_14044]
  · norm_num [dusartPrimeRow_of_explicit_14044]
  · apply DusartPrimeRowsChain.cons
    · norm_num [dusartPrimeRow_of_explicit_14044]
    · norm_num [dusartPrimeRow_of_explicit_14044]
    · apply DusartPrimeRowsChain.cons
      · norm_num [dusartPrimeRow_of_explicit_14044]
      · norm_num [dusartPrimeRow_of_explicit_14044]
      · apply DusartPrimeRowsChain.cons
        · norm_num [dusartPrimeRow_of_explicit_14044]
        · norm_num [dusartPrimeRow_of_explicit_14044]
        · apply DusartPrimeRowsChain.cons
          · norm_num [dusartPrimeRow_of_explicit_14044]
          · norm_num [dusartPrimeRow_of_explicit_14044]
          · apply DusartPrimeRowsChain.cons
            · norm_num [dusartPrimeRow_of_explicit_14044]
            · norm_num [dusartPrimeRow_of_explicit_14044]
            · apply DusartPrimeRowsChain.cons
              · norm_num [dusartPrimeRow_of_explicit_14044]
              · norm_num [dusartPrimeRow_of_explicit_14044]
              · apply DusartPrimeRowsChain.cons
                · norm_num [dusartPrimeRow_of_explicit_14044]
                · norm_num [dusartPrimeRow_of_explicit_14044]
                · apply DusartPrimeRowsChain.empty
                  norm_num [dusartPrimeRow_of_explicit_14044, dusartPrimeRow_of_explicit_right]

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_13367_14050_part02 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_14044 (p := 13451) (q := 13457) (by exact lowPrime_13457) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14044 (p := 13457) (q := 13463) (by exact lowPrime_13463) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14044 (p := 13463) (q := 13469) (by exact lowPrime_13469) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14044 (p := 13469) (q := 13477) (by exact lowPrime_13477) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14044 (p := 13477) (q := 13487) (by exact lowPrime_13487) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14044 (p := 13487) (q := 13499) (by exact lowPrime_13499) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14044 (p := 13499) (q := 13513) (by exact lowPrime_13513) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14044 (p := 13513) (q := 13523) (by exact lowPrime_13523) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_13367_14050_part02_chain :
    DusartPrimeRowsChain 13451 13522 dusartPrimeRows_13367_14050_part02 := by
  apply DusartPrimeRowsChain.cons
  · norm_num [dusartPrimeRow_of_explicit_14044]
  · norm_num [dusartPrimeRow_of_explicit_14044]
  · apply DusartPrimeRowsChain.cons
    · norm_num [dusartPrimeRow_of_explicit_14044]
    · norm_num [dusartPrimeRow_of_explicit_14044]
    · apply DusartPrimeRowsChain.cons
      · norm_num [dusartPrimeRow_of_explicit_14044]
      · norm_num [dusartPrimeRow_of_explicit_14044]
      · apply DusartPrimeRowsChain.cons
        · norm_num [dusartPrimeRow_of_explicit_14044]
        · norm_num [dusartPrimeRow_of_explicit_14044]
        · apply DusartPrimeRowsChain.cons
          · norm_num [dusartPrimeRow_of_explicit_14044]
          · norm_num [dusartPrimeRow_of_explicit_14044]
          · apply DusartPrimeRowsChain.cons
            · norm_num [dusartPrimeRow_of_explicit_14044]
            · norm_num [dusartPrimeRow_of_explicit_14044]
            · apply DusartPrimeRowsChain.cons
              · norm_num [dusartPrimeRow_of_explicit_14044]
              · norm_num [dusartPrimeRow_of_explicit_14044]
              · apply DusartPrimeRowsChain.cons
                · norm_num [dusartPrimeRow_of_explicit_14044]
                · norm_num [dusartPrimeRow_of_explicit_14044]
                · apply DusartPrimeRowsChain.empty
                  norm_num [dusartPrimeRow_of_explicit_14044, dusartPrimeRow_of_explicit_right]

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_13367_14050_part03 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_14044 (p := 13523) (q := 13537) (by exact lowPrime_13537) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14044 (p := 13537) (q := 13553) (by exact lowPrime_13553) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14044 (p := 13553) (q := 13567) (by exact lowPrime_13567) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14044 (p := 13567) (q := 13577) (by exact lowPrime_13577) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14044 (p := 13577) (q := 13591) (by exact lowPrime_13591) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14044 (p := 13591) (q := 13597) (by exact lowPrime_13597) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14044 (p := 13597) (q := 13613) (by exact lowPrime_13613) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14044 (p := 13613) (q := 13619) (by exact lowPrime_13619) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_13367_14050_part03_chain :
    DusartPrimeRowsChain 13523 13618 dusartPrimeRows_13367_14050_part03 := by
  apply DusartPrimeRowsChain.cons
  · norm_num [dusartPrimeRow_of_explicit_14044]
  · norm_num [dusartPrimeRow_of_explicit_14044]
  · apply DusartPrimeRowsChain.cons
    · norm_num [dusartPrimeRow_of_explicit_14044]
    · norm_num [dusartPrimeRow_of_explicit_14044]
    · apply DusartPrimeRowsChain.cons
      · norm_num [dusartPrimeRow_of_explicit_14044]
      · norm_num [dusartPrimeRow_of_explicit_14044]
      · apply DusartPrimeRowsChain.cons
        · norm_num [dusartPrimeRow_of_explicit_14044]
        · norm_num [dusartPrimeRow_of_explicit_14044]
        · apply DusartPrimeRowsChain.cons
          · norm_num [dusartPrimeRow_of_explicit_14044]
          · norm_num [dusartPrimeRow_of_explicit_14044]
          · apply DusartPrimeRowsChain.cons
            · norm_num [dusartPrimeRow_of_explicit_14044]
            · norm_num [dusartPrimeRow_of_explicit_14044]
            · apply DusartPrimeRowsChain.cons
              · norm_num [dusartPrimeRow_of_explicit_14044]
              · norm_num [dusartPrimeRow_of_explicit_14044]
              · apply DusartPrimeRowsChain.cons
                · norm_num [dusartPrimeRow_of_explicit_14044]
                · norm_num [dusartPrimeRow_of_explicit_14044]
                · apply DusartPrimeRowsChain.empty
                  norm_num [dusartPrimeRow_of_explicit_14044, dusartPrimeRow_of_explicit_right]

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_13367_14050_part04 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_14044 (p := 13619) (q := 13627) (by exact lowPrime_13627) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14044 (p := 13627) (q := 13633) (by exact lowPrime_13633) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14044 (p := 13633) (q := 13649) (by exact lowPrime_13649) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14044 (p := 13649) (q := 13669) (by exact lowPrime_13669) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14044 (p := 13669) (q := 13679) (by exact lowPrime_13679) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14044 (p := 13679) (q := 13681) (by exact lowPrime_13681) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14044 (p := 13681) (q := 13687) (by exact lowPrime_13687) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14044 (p := 13687) (q := 13691) (by exact lowPrime_13691) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_13367_14050_part04_chain :
    DusartPrimeRowsChain 13619 13690 dusartPrimeRows_13367_14050_part04 := by
  apply DusartPrimeRowsChain.cons
  · norm_num [dusartPrimeRow_of_explicit_14044]
  · norm_num [dusartPrimeRow_of_explicit_14044]
  · apply DusartPrimeRowsChain.cons
    · norm_num [dusartPrimeRow_of_explicit_14044]
    · norm_num [dusartPrimeRow_of_explicit_14044]
    · apply DusartPrimeRowsChain.cons
      · norm_num [dusartPrimeRow_of_explicit_14044]
      · norm_num [dusartPrimeRow_of_explicit_14044]
      · apply DusartPrimeRowsChain.cons
        · norm_num [dusartPrimeRow_of_explicit_14044]
        · norm_num [dusartPrimeRow_of_explicit_14044]
        · apply DusartPrimeRowsChain.cons
          · norm_num [dusartPrimeRow_of_explicit_14044]
          · norm_num [dusartPrimeRow_of_explicit_14044]
          · apply DusartPrimeRowsChain.cons
            · norm_num [dusartPrimeRow_of_explicit_14044]
            · norm_num [dusartPrimeRow_of_explicit_14044]
            · apply DusartPrimeRowsChain.cons
              · norm_num [dusartPrimeRow_of_explicit_14044]
              · norm_num [dusartPrimeRow_of_explicit_14044]
              · apply DusartPrimeRowsChain.cons
                · norm_num [dusartPrimeRow_of_explicit_14044]
                · norm_num [dusartPrimeRow_of_explicit_14044]
                · apply DusartPrimeRowsChain.empty
                  norm_num [dusartPrimeRow_of_explicit_14044, dusartPrimeRow_of_explicit_right]

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_13367_14050_part05 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_14044 (p := 13691) (q := 13693) (by exact lowPrime_13693) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14044 (p := 13693) (q := 13697) (by exact lowPrime_13697) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14044 (p := 13697) (q := 13709) (by exact lowPrime_13709) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14044 (p := 13709) (q := 13711) (by exact lowPrime_13711) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14044 (p := 13711) (q := 13721) (by exact lowPrime_13721) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14044 (p := 13721) (q := 13723) (by exact lowPrime_13723) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14044 (p := 13723) (q := 13729) (by exact lowPrime_13729) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14044 (p := 13729) (q := 13751) (by exact lowPrime_13751) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_13367_14050_part05_chain :
    DusartPrimeRowsChain 13691 13750 dusartPrimeRows_13367_14050_part05 := by
  apply DusartPrimeRowsChain.cons
  · norm_num [dusartPrimeRow_of_explicit_14044]
  · norm_num [dusartPrimeRow_of_explicit_14044]
  · apply DusartPrimeRowsChain.cons
    · norm_num [dusartPrimeRow_of_explicit_14044]
    · norm_num [dusartPrimeRow_of_explicit_14044]
    · apply DusartPrimeRowsChain.cons
      · norm_num [dusartPrimeRow_of_explicit_14044]
      · norm_num [dusartPrimeRow_of_explicit_14044]
      · apply DusartPrimeRowsChain.cons
        · norm_num [dusartPrimeRow_of_explicit_14044]
        · norm_num [dusartPrimeRow_of_explicit_14044]
        · apply DusartPrimeRowsChain.cons
          · norm_num [dusartPrimeRow_of_explicit_14044]
          · norm_num [dusartPrimeRow_of_explicit_14044]
          · apply DusartPrimeRowsChain.cons
            · norm_num [dusartPrimeRow_of_explicit_14044]
            · norm_num [dusartPrimeRow_of_explicit_14044]
            · apply DusartPrimeRowsChain.cons
              · norm_num [dusartPrimeRow_of_explicit_14044]
              · norm_num [dusartPrimeRow_of_explicit_14044]
              · apply DusartPrimeRowsChain.cons
                · norm_num [dusartPrimeRow_of_explicit_14044]
                · norm_num [dusartPrimeRow_of_explicit_14044]
                · apply DusartPrimeRowsChain.empty
                  norm_num [dusartPrimeRow_of_explicit_14044, dusartPrimeRow_of_explicit_right]

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_13367_14050_part06 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_14044 (p := 13751) (q := 13757) (by exact lowPrime_13757) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14044 (p := 13757) (q := 13759) (by exact lowPrime_13759) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14044 (p := 13759) (q := 13763) (by exact lowPrime_13763) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14044 (p := 13763) (q := 13781) (by exact lowPrime_13781) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14044 (p := 13781) (q := 13789) (by exact lowPrime_13789) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14044 (p := 13789) (q := 13799) (by exact lowPrime_13799) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14044 (p := 13799) (q := 13807) (by exact lowPrime_13807) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14044 (p := 13807) (q := 13829) (by exact lowPrime_13829) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_13367_14050_part06_chain :
    DusartPrimeRowsChain 13751 13828 dusartPrimeRows_13367_14050_part06 := by
  apply DusartPrimeRowsChain.cons
  · norm_num [dusartPrimeRow_of_explicit_14044]
  · norm_num [dusartPrimeRow_of_explicit_14044]
  · apply DusartPrimeRowsChain.cons
    · norm_num [dusartPrimeRow_of_explicit_14044]
    · norm_num [dusartPrimeRow_of_explicit_14044]
    · apply DusartPrimeRowsChain.cons
      · norm_num [dusartPrimeRow_of_explicit_14044]
      · norm_num [dusartPrimeRow_of_explicit_14044]
      · apply DusartPrimeRowsChain.cons
        · norm_num [dusartPrimeRow_of_explicit_14044]
        · norm_num [dusartPrimeRow_of_explicit_14044]
        · apply DusartPrimeRowsChain.cons
          · norm_num [dusartPrimeRow_of_explicit_14044]
          · norm_num [dusartPrimeRow_of_explicit_14044]
          · apply DusartPrimeRowsChain.cons
            · norm_num [dusartPrimeRow_of_explicit_14044]
            · norm_num [dusartPrimeRow_of_explicit_14044]
            · apply DusartPrimeRowsChain.cons
              · norm_num [dusartPrimeRow_of_explicit_14044]
              · norm_num [dusartPrimeRow_of_explicit_14044]
              · apply DusartPrimeRowsChain.cons
                · norm_num [dusartPrimeRow_of_explicit_14044]
                · norm_num [dusartPrimeRow_of_explicit_14044]
                · apply DusartPrimeRowsChain.empty
                  norm_num [dusartPrimeRow_of_explicit_14044, dusartPrimeRow_of_explicit_right]

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_13367_14050_part07 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_14044 (p := 13829) (q := 13831) (by exact lowPrime_13831) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14044 (p := 13831) (q := 13841) (by exact lowPrime_13841) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14044 (p := 13841) (q := 13859) (by exact lowPrime_13859) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14044 (p := 13859) (q := 13873) (by exact lowPrime_13873) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14044 (p := 13873) (q := 13877) (by exact lowPrime_13877) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14044 (p := 13877) (q := 13879) (by exact lowPrime_13879) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14044 (p := 13879) (q := 13883) (by exact lowPrime_13883) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14044 (p := 13883) (q := 13901) (by exact lowPrime_13901) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_13367_14050_part07_chain :
    DusartPrimeRowsChain 13829 13900 dusartPrimeRows_13367_14050_part07 := by
  apply DusartPrimeRowsChain.cons
  · norm_num [dusartPrimeRow_of_explicit_14044]
  · norm_num [dusartPrimeRow_of_explicit_14044]
  · apply DusartPrimeRowsChain.cons
    · norm_num [dusartPrimeRow_of_explicit_14044]
    · norm_num [dusartPrimeRow_of_explicit_14044]
    · apply DusartPrimeRowsChain.cons
      · norm_num [dusartPrimeRow_of_explicit_14044]
      · norm_num [dusartPrimeRow_of_explicit_14044]
      · apply DusartPrimeRowsChain.cons
        · norm_num [dusartPrimeRow_of_explicit_14044]
        · norm_num [dusartPrimeRow_of_explicit_14044]
        · apply DusartPrimeRowsChain.cons
          · norm_num [dusartPrimeRow_of_explicit_14044]
          · norm_num [dusartPrimeRow_of_explicit_14044]
          · apply DusartPrimeRowsChain.cons
            · norm_num [dusartPrimeRow_of_explicit_14044]
            · norm_num [dusartPrimeRow_of_explicit_14044]
            · apply DusartPrimeRowsChain.cons
              · norm_num [dusartPrimeRow_of_explicit_14044]
              · norm_num [dusartPrimeRow_of_explicit_14044]
              · apply DusartPrimeRowsChain.cons
                · norm_num [dusartPrimeRow_of_explicit_14044]
                · norm_num [dusartPrimeRow_of_explicit_14044]
                · apply DusartPrimeRowsChain.empty
                  norm_num [dusartPrimeRow_of_explicit_14044, dusartPrimeRow_of_explicit_right]

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_13367_14050_part08 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_14044 (p := 13901) (q := 13903) (by exact lowPrime_13903) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14044 (p := 13903) (q := 13907) (by exact lowPrime_13907) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14044 (p := 13907) (q := 13913) (by exact lowPrime_13913) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14044 (p := 13913) (q := 13921) (by exact lowPrime_13921) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14044 (p := 13921) (q := 13931) (by exact lowPrime_13931) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14044 (p := 13931) (q := 13933) (by exact lowPrime_13933) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14044 (p := 13933) (q := 13963) (by exact lowPrime_13963) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14044 (p := 13963) (q := 13967) (by exact lowPrime_13967) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_13367_14050_part08_chain :
    DusartPrimeRowsChain 13901 13966 dusartPrimeRows_13367_14050_part08 := by
  apply DusartPrimeRowsChain.cons
  · norm_num [dusartPrimeRow_of_explicit_14044]
  · norm_num [dusartPrimeRow_of_explicit_14044]
  · apply DusartPrimeRowsChain.cons
    · norm_num [dusartPrimeRow_of_explicit_14044]
    · norm_num [dusartPrimeRow_of_explicit_14044]
    · apply DusartPrimeRowsChain.cons
      · norm_num [dusartPrimeRow_of_explicit_14044]
      · norm_num [dusartPrimeRow_of_explicit_14044]
      · apply DusartPrimeRowsChain.cons
        · norm_num [dusartPrimeRow_of_explicit_14044]
        · norm_num [dusartPrimeRow_of_explicit_14044]
        · apply DusartPrimeRowsChain.cons
          · norm_num [dusartPrimeRow_of_explicit_14044]
          · norm_num [dusartPrimeRow_of_explicit_14044]
          · apply DusartPrimeRowsChain.cons
            · norm_num [dusartPrimeRow_of_explicit_14044]
            · norm_num [dusartPrimeRow_of_explicit_14044]
            · apply DusartPrimeRowsChain.cons
              · norm_num [dusartPrimeRow_of_explicit_14044]
              · norm_num [dusartPrimeRow_of_explicit_14044]
              · apply DusartPrimeRowsChain.cons
                · norm_num [dusartPrimeRow_of_explicit_14044]
                · norm_num [dusartPrimeRow_of_explicit_14044]
                · apply DusartPrimeRowsChain.empty
                  norm_num [dusartPrimeRow_of_explicit_14044, dusartPrimeRow_of_explicit_right]

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_13367_14050_part09 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_14044 (p := 13967) (q := 13997) (by exact lowPrime_13997) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14044 (p := 13997) (q := 13999) (by exact lowPrime_13999) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14044 (p := 13999) (q := 14009) (by exact lowPrime_14009) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14044 (p := 14009) (q := 14011) (by exact lowPrime_14011) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14044 (p := 14011) (q := 14029) (by exact lowPrime_14029) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14044 (p := 14029) (q := 14033) (by exact lowPrime_14033) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14044 (p := 14033) (q := 14051) (by exact lowPrime_14051) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_13367_14050_part09_chain :
    DusartPrimeRowsChain 13967 14050 dusartPrimeRows_13367_14050_part09 := by
  apply DusartPrimeRowsChain.cons
  · norm_num [dusartPrimeRow_of_explicit_14044]
  · norm_num [dusartPrimeRow_of_explicit_14044]
  · apply DusartPrimeRowsChain.cons
    · norm_num [dusartPrimeRow_of_explicit_14044]
    · norm_num [dusartPrimeRow_of_explicit_14044]
    · apply DusartPrimeRowsChain.cons
      · norm_num [dusartPrimeRow_of_explicit_14044]
      · norm_num [dusartPrimeRow_of_explicit_14044]
      · apply DusartPrimeRowsChain.cons
        · norm_num [dusartPrimeRow_of_explicit_14044]
        · norm_num [dusartPrimeRow_of_explicit_14044]
        · apply DusartPrimeRowsChain.cons
          · norm_num [dusartPrimeRow_of_explicit_14044]
          · norm_num [dusartPrimeRow_of_explicit_14044]
          · apply DusartPrimeRowsChain.cons
            · norm_num [dusartPrimeRow_of_explicit_14044]
            · norm_num [dusartPrimeRow_of_explicit_14044]
            · apply DusartPrimeRowsChain.cons
              · norm_num [dusartPrimeRow_of_explicit_14044]
              · norm_num [dusartPrimeRow_of_explicit_14044]
              · apply DusartPrimeRowsChain.empty
                norm_num [dusartPrimeRow_of_explicit_14044, dusartPrimeRow_of_explicit_right]

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_14051_14766_part01 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_14764 (p := 14051) (q := 14057) (by exact lowPrime_14057) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14764 (p := 14057) (q := 14071) (by exact lowPrime_14071) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14764 (p := 14071) (q := 14081) (by exact lowPrime_14081) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14764 (p := 14081) (q := 14083) (by exact lowPrime_14083) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14764 (p := 14083) (q := 14087) (by exact lowPrime_14087) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14764 (p := 14087) (q := 14107) (by exact lowPrime_14107) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14764 (p := 14107) (q := 14143) (by exact lowPrime_14143) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14764 (p := 14143) (q := 14149) (by exact lowPrime_14149) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_14051_14766_part01_chain :
    DusartPrimeRowsChain 14051 14148 dusartPrimeRows_14051_14766_part01 := by
  apply DusartPrimeRowsChain.cons
  · norm_num [dusartPrimeRow_of_explicit_14764]
  · norm_num [dusartPrimeRow_of_explicit_14764]
  · apply DusartPrimeRowsChain.cons
    · norm_num [dusartPrimeRow_of_explicit_14764]
    · norm_num [dusartPrimeRow_of_explicit_14764]
    · apply DusartPrimeRowsChain.cons
      · norm_num [dusartPrimeRow_of_explicit_14764]
      · norm_num [dusartPrimeRow_of_explicit_14764]
      · apply DusartPrimeRowsChain.cons
        · norm_num [dusartPrimeRow_of_explicit_14764]
        · norm_num [dusartPrimeRow_of_explicit_14764]
        · apply DusartPrimeRowsChain.cons
          · norm_num [dusartPrimeRow_of_explicit_14764]
          · norm_num [dusartPrimeRow_of_explicit_14764]
          · apply DusartPrimeRowsChain.cons
            · norm_num [dusartPrimeRow_of_explicit_14764]
            · norm_num [dusartPrimeRow_of_explicit_14764]
            · apply DusartPrimeRowsChain.cons
              · norm_num [dusartPrimeRow_of_explicit_14764]
              · norm_num [dusartPrimeRow_of_explicit_14764]
              · apply DusartPrimeRowsChain.cons
                · norm_num [dusartPrimeRow_of_explicit_14764]
                · norm_num [dusartPrimeRow_of_explicit_14764]
                · apply DusartPrimeRowsChain.empty
                  norm_num [dusartPrimeRow_of_explicit_14764, dusartPrimeRow_of_explicit_right]
