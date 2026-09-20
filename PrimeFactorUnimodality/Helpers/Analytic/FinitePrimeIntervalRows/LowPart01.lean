import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowBase

set_option autoImplicit false
set_option maxRecDepth 1000000

/-! # Lower finite Dusart prefix chunk 01 -/

namespace PrimeFactorUnimodality

noncomputable section
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_3299 : Nat.Prime 3299 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 3299 3298 1 2 [2, 17, 97]
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
    · apply IsUnit.of_mul_eq_one (1649 : ZMod 3299)
      decide
    · apply IsUnit.of_mul_eq_one (2551 : ZMod 3299)
      decide
    · apply IsUnit.of_mul_eq_one (2776 : ZMod 3299)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_3301 : Nat.Prime 3301 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 3301 3300 1 6 [2, 2, 3, 5, 5, 11]
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
    · apply IsUnit.of_mul_eq_one (1650 : ZMod 3301)
      decide
    · apply IsUnit.of_mul_eq_one (2725 : ZMod 3301)
      decide
    · apply IsUnit.of_mul_eq_one (233 : ZMod 3301)
      decide
    · apply IsUnit.of_mul_eq_one (2209 : ZMod 3301)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_3307 : Nat.Prime 3307 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 3307 3306 1 2 [2, 3, 19, 29]
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
    · apply IsUnit.of_mul_eq_one (1653 : ZMod 3307)
      decide
    · apply IsUnit.of_mul_eq_one (2185 : ZMod 3307)
      decide
    · apply IsUnit.of_mul_eq_one (264 : ZMod 3307)
      decide
    · apply IsUnit.of_mul_eq_one (3069 : ZMod 3307)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_3313 : Nat.Prime 3313 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 3313 3312 1 10 [2, 2, 2, 2, 3, 3, 23]
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
    · apply IsUnit.of_mul_eq_one (1656 : ZMod 3313)
      decide
    · apply IsUnit.of_mul_eq_one (2938 : ZMod 3313)
      decide
    · apply IsUnit.of_mul_eq_one (1903 : ZMod 3313)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_3319 : Nat.Prime 3319 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 3319 3318 1 6 [2, 3, 7, 79]
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
    · apply IsUnit.of_mul_eq_one (1659 : ZMod 3319)
      decide
    · apply IsUnit.of_mul_eq_one (1703 : ZMod 3319)
      decide
    · apply IsUnit.of_mul_eq_one (166 : ZMod 3319)
      decide
    · apply IsUnit.of_mul_eq_one (1821 : ZMod 3319)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_3323 : Nat.Prime 3323 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 3323 3322 1 2 [2, 11, 151]
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
    · apply IsUnit.of_mul_eq_one (1661 : ZMod 3323)
      decide
    · apply IsUnit.of_mul_eq_one (600 : ZMod 3323)
      decide
    · apply IsUnit.of_mul_eq_one (1340 : ZMod 3323)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_3329 : Nat.Prime 3329 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 3329 3328 1 3 [2, 2, 2, 2, 2, 2, 2, 2, 13]
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
    rcases hq with rfl | rfl
    · apply IsUnit.of_mul_eq_one (1664 : ZMod 3329)
      decide
    · apply IsUnit.of_mul_eq_one (823 : ZMod 3329)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_3331 : Nat.Prime 3331 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 3331 3330 1 3 [2, 3, 3, 5, 37]
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
    · apply IsUnit.of_mul_eq_one (1665 : ZMod 3331)
      decide
    · apply IsUnit.of_mul_eq_one (2708 : ZMod 3331)
      decide
    · apply IsUnit.of_mul_eq_one (558 : ZMod 3331)
      decide
    · apply IsUnit.of_mul_eq_one (325 : ZMod 3331)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_3343 : Nat.Prime 3343 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 3343 3342 1 5 [2, 3, 557]
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
    · apply IsUnit.of_mul_eq_one (1671 : ZMod 3343)
      decide
    · apply IsUnit.of_mul_eq_one (2703 : ZMod 3343)
      decide
    · apply IsUnit.of_mul_eq_one (1385 : ZMod 3343)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_3347 : Nat.Prime 3347 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 3347 3346 1 2 [2, 7, 239]
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
    · apply IsUnit.of_mul_eq_one (1673 : ZMod 3347)
      decide
    · apply IsUnit.of_mul_eq_one (2540 : ZMod 3347)
      decide
    · apply IsUnit.of_mul_eq_one (561 : ZMod 3347)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_3359 : Nat.Prime 3359 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 3359 3358 1 11 [2, 23, 73]
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
    · apply IsUnit.of_mul_eq_one (1679 : ZMod 3359)
      decide
    · apply IsUnit.of_mul_eq_one (2555 : ZMod 3359)
      decide
    · apply IsUnit.of_mul_eq_one (1249 : ZMod 3359)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_3361 : Nat.Prime 3361 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 3361 3360 1 22 [2, 2, 2, 2, 2, 3, 5, 7]
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
    · apply IsUnit.of_mul_eq_one (1680 : ZMod 3361)
      decide
    · apply IsUnit.of_mul_eq_one (297 : ZMod 3361)
      decide
    · apply IsUnit.of_mul_eq_one (3209 : ZMod 3361)
      decide
    · apply IsUnit.of_mul_eq_one (917 : ZMod 3361)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_3371 : Nat.Prime 3371 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 3371 3370 1 2 [2, 5, 337]
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
    · apply IsUnit.of_mul_eq_one (1685 : ZMod 3371)
      decide
    · apply IsUnit.of_mul_eq_one (1563 : ZMod 3371)
      decide
    · apply IsUnit.of_mul_eq_one (1239 : ZMod 3371)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_3373 : Nat.Prime 3373 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 3373 3372 1 5 [2, 2, 3, 281]
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
    · apply IsUnit.of_mul_eq_one (1686 : ZMod 3373)
      decide
    · apply IsUnit.of_mul_eq_one (1342 : ZMod 3373)
      decide
    · apply IsUnit.of_mul_eq_one (607 : ZMod 3373)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_3389 : Nat.Prime 3389 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 3389 3388 1 3 [2, 2, 7, 11, 11]
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
    · apply IsUnit.of_mul_eq_one (1694 : ZMod 3389)
      decide
    · apply IsUnit.of_mul_eq_one (1341 : ZMod 3389)
      decide
    · apply IsUnit.of_mul_eq_one (1674 : ZMod 3389)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_3391 : Nat.Prime 3391 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 3391 3390 1 3 [2, 3, 5, 113]
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
    · apply IsUnit.of_mul_eq_one (1695 : ZMod 3391)
      decide
    · apply IsUnit.of_mul_eq_one (1315 : ZMod 3391)
      decide
    · apply IsUnit.of_mul_eq_one (1689 : ZMod 3391)
      decide
    · apply IsUnit.of_mul_eq_one (2710 : ZMod 3391)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_3407 : Nat.Prime 3407 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 3407 3406 1 5 [2, 13, 131]
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
    · apply IsUnit.of_mul_eq_one (1703 : ZMod 3407)
      decide
    · apply IsUnit.of_mul_eq_one (1695 : ZMod 3407)
      decide
    · apply IsUnit.of_mul_eq_one (2199 : ZMod 3407)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_3413 : Nat.Prime 3413 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 3413 3412 1 2 [2, 2, 853]
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
    · apply IsUnit.of_mul_eq_one (1706 : ZMod 3413)
      decide
    · apply IsUnit.of_mul_eq_one (2958 : ZMod 3413)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_3433 : Nat.Prime 3433 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 3433 3432 1 5 [2, 2, 2, 3, 11, 13]
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
    · apply IsUnit.of_mul_eq_one (1716 : ZMod 3433)
      decide
    · apply IsUnit.of_mul_eq_one (3343 : ZMod 3433)
      decide
    · apply IsUnit.of_mul_eq_one (2907 : ZMod 3433)
      decide
    · apply IsUnit.of_mul_eq_one (1746 : ZMod 3433)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_3449 : Nat.Prime 3449 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 3449 3448 1 3 [2, 2, 2, 431]
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
    · apply IsUnit.of_mul_eq_one (1724 : ZMod 3449)
      decide
    · apply IsUnit.of_mul_eq_one (500 : ZMod 3449)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_3457 : Nat.Prime 3457 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 3457 3456 1 7 [2, 2, 2, 2, 2, 2, 2, 3, 3, 3]
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
    rcases hq with rfl | rfl
    · apply IsUnit.of_mul_eq_one (1728 : ZMod 3457)
      decide
    · apply IsUnit.of_mul_eq_one (911 : ZMod 3457)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_3461 : Nat.Prime 3461 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 3461 3460 1 2 [2, 2, 5, 173]
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
    · apply IsUnit.of_mul_eq_one (1730 : ZMod 3461)
      decide
    · apply IsUnit.of_mul_eq_one (3335 : ZMod 3461)
      decide
    · apply IsUnit.of_mul_eq_one (2083 : ZMod 3461)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_3463 : Nat.Prime 3463 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 3463 3462 1 3 [2, 3, 577]
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
    · apply IsUnit.of_mul_eq_one (1731 : ZMod 3463)
      decide
    · apply IsUnit.of_mul_eq_one (3340 : ZMod 3463)
      decide
    · apply IsUnit.of_mul_eq_one (2250 : ZMod 3463)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_3467 : Nat.Prime 3467 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 3467 3466 1 2 [2, 1733]
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
    · apply IsUnit.of_mul_eq_one (1733 : ZMod 3467)
      decide
    · apply IsUnit.of_mul_eq_one (1156 : ZMod 3467)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_3469 : Nat.Prime 3469 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 3469 3468 1 2 [2, 2, 3, 17, 17]
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
    · apply IsUnit.of_mul_eq_one (1734 : ZMod 3469)
      decide
    · apply IsUnit.of_mul_eq_one (1717 : ZMod 3469)
      decide
    · apply IsUnit.of_mul_eq_one (371 : ZMod 3469)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_3491 : Nat.Prime 3491 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 3491 3490 1 2 [2, 5, 349]
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
    · apply IsUnit.of_mul_eq_one (1745 : ZMod 3491)
      decide
    · apply IsUnit.of_mul_eq_one (1842 : ZMod 3491)
      decide
    · apply IsUnit.of_mul_eq_one (3218 : ZMod 3491)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_3499 : Nat.Prime 3499 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 3499 3498 1 2 [2, 3, 11, 53]
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
    · apply IsUnit.of_mul_eq_one (1749 : ZMod 3499)
      decide
    · apply IsUnit.of_mul_eq_one (2280 : ZMod 3499)
      decide
    · apply IsUnit.of_mul_eq_one (2443 : ZMod 3499)
      decide
    · apply IsUnit.of_mul_eq_one (747 : ZMod 3499)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_3511 : Nat.Prime 3511 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 3511 3510 1 7 [2, 3, 3, 3, 5, 13]
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
    · apply IsUnit.of_mul_eq_one (1755 : ZMod 3511)
      decide
    · apply IsUnit.of_mul_eq_one (1422 : ZMod 3511)
      decide
    · apply IsUnit.of_mul_eq_one (1130 : ZMod 3511)
      decide
    · apply IsUnit.of_mul_eq_one (2165 : ZMod 3511)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_3517 : Nat.Prime 3517 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 3517 3516 1 2 [2, 2, 3, 293]
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
    · apply IsUnit.of_mul_eq_one (1758 : ZMod 3517)
      decide
    · apply IsUnit.of_mul_eq_one (2258 : ZMod 3517)
      decide
    · apply IsUnit.of_mul_eq_one (3158 : ZMod 3517)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_3527 : Nat.Prime 3527 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 3527 3526 1 5 [2, 41, 43]
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
    · apply IsUnit.of_mul_eq_one (1763 : ZMod 3527)
      decide
    · apply IsUnit.of_mul_eq_one (1907 : ZMod 3527)
      decide
    · apply IsUnit.of_mul_eq_one (2318 : ZMod 3527)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_3529 : Nat.Prime 3529 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 3529 3528 1 17 [2, 2, 2, 3, 3, 7, 7]
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
    · apply IsUnit.of_mul_eq_one (1764 : ZMod 3529)
      decide
    · apply IsUnit.of_mul_eq_one (149 : ZMod 3529)
      decide
    · apply IsUnit.of_mul_eq_one (257 : ZMod 3529)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_3533 : Nat.Prime 3533 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 3533 3532 1 2 [2, 2, 883]
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
    · apply IsUnit.of_mul_eq_one (1766 : ZMod 3533)
      decide
    · apply IsUnit.of_mul_eq_one (3062 : ZMod 3533)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_3539 : Nat.Prime 3539 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 3539 3538 1 2 [2, 29, 61]
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
    · apply IsUnit.of_mul_eq_one (1769 : ZMod 3539)
      decide
    · apply IsUnit.of_mul_eq_one (1358 : ZMod 3539)
      decide
    · apply IsUnit.of_mul_eq_one (752 : ZMod 3539)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_3541 : Nat.Prime 3541 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 3541 3540 1 7 [2, 2, 3, 5, 59]
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
    · apply IsUnit.of_mul_eq_one (1770 : ZMod 3541)
      decide
    · apply IsUnit.of_mul_eq_one (1160 : ZMod 3541)
      decide
    · apply IsUnit.of_mul_eq_one (2944 : ZMod 3541)
      decide
    · apply IsUnit.of_mul_eq_one (1894 : ZMod 3541)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_3547 : Nat.Prime 3547 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 3547 3546 1 2 [2, 3, 3, 197]
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
    · apply IsUnit.of_mul_eq_one (1773 : ZMod 3547)
      decide
    · apply IsUnit.of_mul_eq_one (387 : ZMod 3547)
      decide
    · apply IsUnit.of_mul_eq_one (3367 : ZMod 3547)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_3557 : Nat.Prime 3557 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 3557 3556 1 2 [2, 2, 7, 127]
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
    · apply IsUnit.of_mul_eq_one (1778 : ZMod 3557)
      decide
    · apply IsUnit.of_mul_eq_one (1143 : ZMod 3557)
      decide
    · apply IsUnit.of_mul_eq_one (1741 : ZMod 3557)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_3559 : Nat.Prime 3559 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 3559 3558 1 3 [2, 3, 593]
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
    · apply IsUnit.of_mul_eq_one (1779 : ZMod 3559)
      decide
    · apply IsUnit.of_mul_eq_one (478 : ZMod 3559)
      decide
    · apply IsUnit.of_mul_eq_one (44 : ZMod 3559)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_3571 : Nat.Prime 3571 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 3571 3570 1 2 [2, 3, 5, 7, 17]
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
    · apply IsUnit.of_mul_eq_one (1785 : ZMod 3571)
      decide
    · apply IsUnit.of_mul_eq_one (34 : ZMod 3571)
      decide
    · apply IsUnit.of_mul_eq_one (2066 : ZMod 3571)
      decide
    · apply IsUnit.of_mul_eq_one (936 : ZMod 3571)
      decide
    · apply IsUnit.of_mul_eq_one (1151 : ZMod 3571)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_3581 : Nat.Prime 3581 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 3581 3580 1 2 [2, 2, 5, 179]
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
    · apply IsUnit.of_mul_eq_one (1790 : ZMod 3581)
      decide
    · apply IsUnit.of_mul_eq_one (1290 : ZMod 3581)
      decide
    · apply IsUnit.of_mul_eq_one (1649 : ZMod 3581)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_3583 : Nat.Prime 3583 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 3583 3582 1 3 [2, 3, 3, 199]
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
    · apply IsUnit.of_mul_eq_one (1791 : ZMod 3583)
      decide
    · apply IsUnit.of_mul_eq_one (2042 : ZMod 3583)
      decide
    · apply IsUnit.of_mul_eq_one (52 : ZMod 3583)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_3593 : Nat.Prime 3593 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 3593 3592 1 3 [2, 2, 2, 449]
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
    · apply IsUnit.of_mul_eq_one (1796 : ZMod 3593)
      decide
    · apply IsUnit.of_mul_eq_one (2072 : ZMod 3593)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_3607 : Nat.Prime 3607 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 3607 3606 1 5 [2, 3, 601]
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
    · apply IsUnit.of_mul_eq_one (1803 : ZMod 3607)
      decide
    · apply IsUnit.of_mul_eq_one (3140 : ZMod 3607)
      decide
    · apply IsUnit.of_mul_eq_one (3417 : ZMod 3607)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_3613 : Nat.Prime 3613 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 3613 3612 1 2 [2, 2, 3, 7, 43]
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
    · apply IsUnit.of_mul_eq_one (1806 : ZMod 3613)
      decide
    · apply IsUnit.of_mul_eq_one (558 : ZMod 3613)
      decide
    · apply IsUnit.of_mul_eq_one (636 : ZMod 3613)
      decide
    · apply IsUnit.of_mul_eq_one (3172 : ZMod 3613)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_3617 : Nat.Prime 3617 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 3617 3616 1 3 [2, 2, 2, 2, 2, 113]
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
    · apply IsUnit.of_mul_eq_one (1808 : ZMod 3617)
      decide
    · apply IsUnit.of_mul_eq_one (3522 : ZMod 3617)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_3623 : Nat.Prime 3623 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 3623 3622 1 5 [2, 1811]
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
    · apply IsUnit.of_mul_eq_one (1811 : ZMod 3623)
      decide
    · apply IsUnit.of_mul_eq_one (151 : ZMod 3623)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_3631 : Nat.Prime 3631 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 3631 3630 1 15 [2, 3, 5, 11, 11]
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
    · apply IsUnit.of_mul_eq_one (1815 : ZMod 3631)
      decide
    · apply IsUnit.of_mul_eq_one (2532 : ZMod 3631)
      decide
    · apply IsUnit.of_mul_eq_one (3135 : ZMod 3631)
      decide
    · apply IsUnit.of_mul_eq_one (216 : ZMod 3631)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_3637 : Nat.Prime 3637 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 3637 3636 1 2 [2, 2, 3, 3, 101]
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
    · apply IsUnit.of_mul_eq_one (1818 : ZMod 3637)
      decide
    · apply IsUnit.of_mul_eq_one (2656 : ZMod 3637)
      decide
    · apply IsUnit.of_mul_eq_one (840 : ZMod 3637)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_3643 : Nat.Prime 3643 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 3643 3642 1 2 [2, 3, 607]
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
    · apply IsUnit.of_mul_eq_one (1821 : ZMod 3643)
      decide
    · apply IsUnit.of_mul_eq_one (1073 : ZMod 3643)
      decide
    · apply IsUnit.of_mul_eq_one (1330 : ZMod 3643)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_3659 : Nat.Prime 3659 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 3659 3658 1 2 [2, 31, 59]
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
    · apply IsUnit.of_mul_eq_one (1829 : ZMod 3659)
      decide
    · apply IsUnit.of_mul_eq_one (3320 : ZMod 3659)
      decide
    · apply IsUnit.of_mul_eq_one (446 : ZMod 3659)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_3671 : Nat.Prime 3671 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 3671 3670 1 13 [2, 5, 367]
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
    · apply IsUnit.of_mul_eq_one (1835 : ZMod 3671)
      decide
    · apply IsUnit.of_mul_eq_one (3015 : ZMod 3671)
      decide
    · apply IsUnit.of_mul_eq_one (1851 : ZMod 3671)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_3673 : Nat.Prime 3673 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 3673 3672 1 5 [2, 2, 2, 3, 3, 3, 17]
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
    · apply IsUnit.of_mul_eq_one (1836 : ZMod 3673)
      decide
    · apply IsUnit.of_mul_eq_one (2832 : ZMod 3673)
      decide
    · apply IsUnit.of_mul_eq_one (2110 : ZMod 3673)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_3677 : Nat.Prime 3677 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 3677 3676 1 2 [2, 2, 919]
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
    · apply IsUnit.of_mul_eq_one (1838 : ZMod 3677)
      decide
    · apply IsUnit.of_mul_eq_one (1716 : ZMod 3677)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_3691 : Nat.Prime 3691 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 3691 3690 1 2 [2, 3, 3, 5, 41]
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
    · apply IsUnit.of_mul_eq_one (1845 : ZMod 3691)
      decide
    · apply IsUnit.of_mul_eq_one (1388 : ZMod 3691)
      decide
    · apply IsUnit.of_mul_eq_one (1857 : ZMod 3691)
      decide
    · apply IsUnit.of_mul_eq_one (3027 : ZMod 3691)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_3697 : Nat.Prime 3697 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 3697 3696 1 5 [2, 2, 2, 2, 3, 7, 11]
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
    rcases hq with rfl | rfl | rfl | rfl
    · apply IsUnit.of_mul_eq_one (1848 : ZMod 3697)
      decide
    · apply IsUnit.of_mul_eq_one (2291 : ZMod 3697)
      decide
    · apply IsUnit.of_mul_eq_one (2433 : ZMod 3697)
      decide
    · apply IsUnit.of_mul_eq_one (3232 : ZMod 3697)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_3701 : Nat.Prime 3701 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 3701 3700 1 2 [2, 2, 5, 5, 37]
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
    · apply IsUnit.of_mul_eq_one (1850 : ZMod 3701)
      decide
    · apply IsUnit.of_mul_eq_one (465 : ZMod 3701)
      decide
    · apply IsUnit.of_mul_eq_one (2101 : ZMod 3701)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_3709 : Nat.Prime 3709 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 3709 3708 1 2 [2, 2, 3, 3, 103]
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
    · apply IsUnit.of_mul_eq_one (1854 : ZMod 3709)
      decide
    · apply IsUnit.of_mul_eq_one (2306 : ZMod 3709)
      decide
    · apply IsUnit.of_mul_eq_one (2326 : ZMod 3709)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_3719 : Nat.Prime 3719 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 3719 3718 1 7 [2, 11, 13, 13]
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
    · apply IsUnit.of_mul_eq_one (1859 : ZMod 3719)
      decide
    · apply IsUnit.of_mul_eq_one (2161 : ZMod 3719)
      decide
    · apply IsUnit.of_mul_eq_one (2836 : ZMod 3719)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_3727 : Nat.Prime 3727 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 3727 3726 1 3 [2, 3, 3, 3, 3, 23]
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
    · apply IsUnit.of_mul_eq_one (1863 : ZMod 3727)
      decide
    · apply IsUnit.of_mul_eq_one (1638 : ZMod 3727)
      decide
    · apply IsUnit.of_mul_eq_one (3421 : ZMod 3727)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_3733 : Nat.Prime 3733 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 3733 3732 1 2 [2, 2, 3, 311]
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
    · apply IsUnit.of_mul_eq_one (1866 : ZMod 3733)
      decide
    · apply IsUnit.of_mul_eq_one (2172 : ZMod 3733)
      decide
    · apply IsUnit.of_mul_eq_one (1949 : ZMod 3733)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_3739 : Nat.Prime 3739 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 3739 3738 1 7 [2, 3, 7, 89]
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
    · apply IsUnit.of_mul_eq_one (1869 : ZMod 3739)
      decide
    · apply IsUnit.of_mul_eq_one (231 : ZMod 3739)
      decide
    · apply IsUnit.of_mul_eq_one (2631 : ZMod 3739)
      decide
    · apply IsUnit.of_mul_eq_one (1859 : ZMod 3739)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_3761 : Nat.Prime 3761 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 3761 3760 1 3 [2, 2, 2, 2, 5, 47]
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
    · apply IsUnit.of_mul_eq_one (1880 : ZMod 3761)
      decide
    · apply IsUnit.of_mul_eq_one (1947 : ZMod 3761)
      decide
    · apply IsUnit.of_mul_eq_one (1463 : ZMod 3761)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_3767 : Nat.Prime 3767 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 3767 3766 1 5 [2, 7, 269]
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
    · apply IsUnit.of_mul_eq_one (1883 : ZMod 3767)
      decide
    · apply IsUnit.of_mul_eq_one (1788 : ZMod 3767)
      decide
    · apply IsUnit.of_mul_eq_one (2468 : ZMod 3767)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_3769 : Nat.Prime 3769 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 3769 3768 1 7 [2, 2, 2, 3, 157]
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
    · apply IsUnit.of_mul_eq_one (1884 : ZMod 3769)
      decide
    · apply IsUnit.of_mul_eq_one (154 : ZMod 3769)
      decide
    · apply IsUnit.of_mul_eq_one (3425 : ZMod 3769)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_3779 : Nat.Prime 3779 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 3779 3778 1 2 [2, 1889]
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
    · apply IsUnit.of_mul_eq_one (1889 : ZMod 3779)
      decide
    · apply IsUnit.of_mul_eq_one (1260 : ZMod 3779)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_3793 : Nat.Prime 3793 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 3793 3792 1 5 [2, 2, 2, 2, 3, 79]
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
    · apply IsUnit.of_mul_eq_one (1896 : ZMod 3793)
      decide
    · apply IsUnit.of_mul_eq_one (2172 : ZMod 3793)
      decide
    · apply IsUnit.of_mul_eq_one (1569 : ZMod 3793)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_3797 : Nat.Prime 3797 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 3797 3796 1 2 [2, 2, 13, 73]
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
    · apply IsUnit.of_mul_eq_one (1898 : ZMod 3797)
      decide
    · apply IsUnit.of_mul_eq_one (2059 : ZMod 3797)
      decide
    · apply IsUnit.of_mul_eq_one (3357 : ZMod 3797)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_3803 : Nat.Prime 3803 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 3803 3802 1 2 [2, 1901]
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
    · apply IsUnit.of_mul_eq_one (1901 : ZMod 3803)
      decide
    · apply IsUnit.of_mul_eq_one (1268 : ZMod 3803)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_3821 : Nat.Prime 3821 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 3821 3820 1 3 [2, 2, 5, 191]
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
    · apply IsUnit.of_mul_eq_one (1910 : ZMod 3821)
      decide
    · apply IsUnit.of_mul_eq_one (1350 : ZMod 3821)
      decide
    · apply IsUnit.of_mul_eq_one (2270 : ZMod 3821)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_3823 : Nat.Prime 3823 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 3823 3822 1 3 [2, 3, 7, 7, 13]
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
    · apply IsUnit.of_mul_eq_one (1911 : ZMod 3823)
      decide
    · apply IsUnit.of_mul_eq_one (2943 : ZMod 3823)
      decide
    · apply IsUnit.of_mul_eq_one (1305 : ZMod 3823)
      decide
    · apply IsUnit.of_mul_eq_one (1194 : ZMod 3823)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_3833 : Nat.Prime 3833 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 3833 3832 1 3 [2, 2, 2, 479]
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
    · apply IsUnit.of_mul_eq_one (1916 : ZMod 3833)
      decide
    · apply IsUnit.of_mul_eq_one (3379 : ZMod 3833)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_3847 : Nat.Prime 3847 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 3847 3846 1 5 [2, 3, 641]
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
    · apply IsUnit.of_mul_eq_one (1923 : ZMod 3847)
      decide
    · apply IsUnit.of_mul_eq_one (3195 : ZMod 3847)
      decide
    · apply IsUnit.of_mul_eq_one (1842 : ZMod 3847)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_3851 : Nat.Prime 3851 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 3851 3850 1 2 [2, 5, 5, 7, 11]
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
    · apply IsUnit.of_mul_eq_one (1925 : ZMod 3851)
      decide
    · apply IsUnit.of_mul_eq_one (3803 : ZMod 3851)
      decide
    · apply IsUnit.of_mul_eq_one (2535 : ZMod 3851)
      decide
    · apply IsUnit.of_mul_eq_one (2407 : ZMod 3851)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_3853 : Nat.Prime 3853 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 3853 3852 1 2 [2, 2, 3, 3, 107]
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
    · apply IsUnit.of_mul_eq_one (1926 : ZMod 3853)
      decide
    · apply IsUnit.of_mul_eq_one (2948 : ZMod 3853)
      decide
    · apply IsUnit.of_mul_eq_one (1765 : ZMod 3853)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_3863 : Nat.Prime 3863 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 3863 3862 1 5 [2, 1931]
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
    · apply IsUnit.of_mul_eq_one (1931 : ZMod 3863)
      decide
    · apply IsUnit.of_mul_eq_one (161 : ZMod 3863)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_3877 : Nat.Prime 3877 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 3877 3876 1 2 [2, 2, 3, 17, 19]
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
    · apply IsUnit.of_mul_eq_one (1938 : ZMod 3877)
      decide
    · apply IsUnit.of_mul_eq_one (1217 : ZMod 3877)
      decide
    · apply IsUnit.of_mul_eq_one (2439 : ZMod 3877)
      decide
    · apply IsUnit.of_mul_eq_one (3474 : ZMod 3877)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_3881 : Nat.Prime 3881 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 3881 3880 1 13 [2, 2, 2, 5, 97]
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
    · apply IsUnit.of_mul_eq_one (1940 : ZMod 3881)
      decide
    · apply IsUnit.of_mul_eq_one (1358 : ZMod 3881)
      decide
    · apply IsUnit.of_mul_eq_one (2283 : ZMod 3881)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_3889 : Nat.Prime 3889 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 3889 3888 1 11 [2, 2, 2, 2, 3, 3, 3, 3, 3]
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
    rcases hq with rfl | rfl
    · apply IsUnit.of_mul_eq_one (1944 : ZMod 3889)
      decide
    · apply IsUnit.of_mul_eq_one (1962 : ZMod 3889)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_3907 : Nat.Prime 3907 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 3907 3906 1 2 [2, 3, 3, 7, 31]
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
    · apply IsUnit.of_mul_eq_one (1953 : ZMod 3907)
      decide
    · apply IsUnit.of_mul_eq_one (2625 : ZMod 3907)
      decide
    · apply IsUnit.of_mul_eq_one (90 : ZMod 3907)
      decide
    · apply IsUnit.of_mul_eq_one (832 : ZMod 3907)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_3911 : Nat.Prime 3911 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 3911 3910 1 13 [2, 5, 17, 23]
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
    · apply IsUnit.of_mul_eq_one (1955 : ZMod 3911)
      decide
    · apply IsUnit.of_mul_eq_one (2216 : ZMod 3911)
      decide
    · apply IsUnit.of_mul_eq_one (3501 : ZMod 3911)
      decide
    · apply IsUnit.of_mul_eq_one (1104 : ZMod 3911)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_3917 : Nat.Prime 3917 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 3917 3916 1 2 [2, 2, 11, 89]
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
    · apply IsUnit.of_mul_eq_one (1958 : ZMod 3917)
      decide
    · apply IsUnit.of_mul_eq_one (312 : ZMod 3917)
      decide
    · apply IsUnit.of_mul_eq_one (853 : ZMod 3917)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_3919 : Nat.Prime 3919 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 3919 3918 1 3 [2, 3, 653]
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
    · apply IsUnit.of_mul_eq_one (1959 : ZMod 3919)
      decide
    · apply IsUnit.of_mul_eq_one (3002 : ZMod 3919)
      decide
    · apply IsUnit.of_mul_eq_one (3020 : ZMod 3919)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_3923 : Nat.Prime 3923 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 3923 3922 1 2 [2, 37, 53]
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
    · apply IsUnit.of_mul_eq_one (1961 : ZMod 3923)
      decide
    · apply IsUnit.of_mul_eq_one (2009 : ZMod 3923)
      decide
    · apply IsUnit.of_mul_eq_one (1754 : ZMod 3923)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_3929 : Nat.Prime 3929 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 3929 3928 1 3 [2, 2, 2, 491]
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
    · apply IsUnit.of_mul_eq_one (1964 : ZMod 3929)
      decide
    · apply IsUnit.of_mul_eq_one (2582 : ZMod 3929)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_3931 : Nat.Prime 3931 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 3931 3930 1 2 [2, 3, 5, 131]
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
    · apply IsUnit.of_mul_eq_one (1965 : ZMod 3931)
      decide
    · apply IsUnit.of_mul_eq_one (2826 : ZMod 3931)
      decide
    · apply IsUnit.of_mul_eq_one (2173 : ZMod 3931)
      decide
    · apply IsUnit.of_mul_eq_one (704 : ZMod 3931)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_3943 : Nat.Prime 3943 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 3943 3942 1 3 [2, 3, 3, 3, 73]
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
    · apply IsUnit.of_mul_eq_one (1971 : ZMod 3943)
      decide
    · apply IsUnit.of_mul_eq_one (3564 : ZMod 3943)
      decide
    · apply IsUnit.of_mul_eq_one (2318 : ZMod 3943)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_3947 : Nat.Prime 3947 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 3947 3946 1 2 [2, 1973]
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
    · apply IsUnit.of_mul_eq_one (1973 : ZMod 3947)
      decide
    · apply IsUnit.of_mul_eq_one (1316 : ZMod 3947)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_3967 : Nat.Prime 3967 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 3967 3966 1 6 [2, 3, 661]
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
    · apply IsUnit.of_mul_eq_one (1983 : ZMod 3967)
      decide
    · apply IsUnit.of_mul_eq_one (2348 : ZMod 3967)
      decide
    · apply IsUnit.of_mul_eq_one (464 : ZMod 3967)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_3989 : Nat.Prime 3989 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 3989 3988 1 2 [2, 2, 997]
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
    · apply IsUnit.of_mul_eq_one (1994 : ZMod 3989)
      decide
    · apply IsUnit.of_mul_eq_one (266 : ZMod 3989)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_4001 : Nat.Prime 4001 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 4001 4000 1 3 [2, 2, 2, 2, 2, 5, 5, 5]
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
    · apply IsUnit.of_mul_eq_one (2000 : ZMod 4001)
      decide
    · apply IsUnit.of_mul_eq_one (2855 : ZMod 4001)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_4003 : Nat.Prime 4003 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 4003 4002 1 2 [2, 3, 23, 29]
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
    · apply IsUnit.of_mul_eq_one (2001 : ZMod 4003)
      decide
    · apply IsUnit.of_mul_eq_one (2394 : ZMod 4003)
      decide
    · apply IsUnit.of_mul_eq_one (1961 : ZMod 4003)
      decide
    · apply IsUnit.of_mul_eq_one (1192 : ZMod 4003)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_4007 : Nat.Prime 4007 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 4007 4006 1 5 [2, 2003]
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
    · apply IsUnit.of_mul_eq_one (2003 : ZMod 4007)
      decide
    · apply IsUnit.of_mul_eq_one (167 : ZMod 4007)
      decide
  · norm_num
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_3275_3802_part01 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_3802 (p := 3275) (q := 3299) (by exact lowPrime_3299) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_3802 (p := 3299) (q := 3301) (by exact lowPrime_3301) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_3802 (p := 3301) (q := 3307) (by exact lowPrime_3307) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_3802 (p := 3307) (q := 3313) (by exact lowPrime_3313) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_3802 (p := 3313) (q := 3319) (by exact lowPrime_3319) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_3802 (p := 3319) (q := 3323) (by exact lowPrime_3323) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_3802 (p := 3323) (q := 3329) (by exact lowPrime_3329) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_3802 (p := 3329) (q := 3331) (by exact lowPrime_3331) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_3275_3802_part01_chain :
    DusartPrimeRowsChain 3275 3330 dusartPrimeRows_3275_3802_part01 := by
  apply DusartPrimeRowsChain.cons
  · norm_num [dusartPrimeRow_of_explicit_3802]
  · norm_num [dusartPrimeRow_of_explicit_3802]
  · apply DusartPrimeRowsChain.cons
    · norm_num [dusartPrimeRow_of_explicit_3802]
    · norm_num [dusartPrimeRow_of_explicit_3802]
    · apply DusartPrimeRowsChain.cons
      · norm_num [dusartPrimeRow_of_explicit_3802]
      · norm_num [dusartPrimeRow_of_explicit_3802]
      · apply DusartPrimeRowsChain.cons
        · norm_num [dusartPrimeRow_of_explicit_3802]
        · norm_num [dusartPrimeRow_of_explicit_3802]
        · apply DusartPrimeRowsChain.cons
          · norm_num [dusartPrimeRow_of_explicit_3802]
          · norm_num [dusartPrimeRow_of_explicit_3802]
          · apply DusartPrimeRowsChain.cons
            · norm_num [dusartPrimeRow_of_explicit_3802]
            · norm_num [dusartPrimeRow_of_explicit_3802]
            · apply DusartPrimeRowsChain.cons
              · norm_num [dusartPrimeRow_of_explicit_3802]
              · norm_num [dusartPrimeRow_of_explicit_3802]
              · apply DusartPrimeRowsChain.cons
                · norm_num [dusartPrimeRow_of_explicit_3802]
                · norm_num [dusartPrimeRow_of_explicit_3802]
                · apply DusartPrimeRowsChain.empty
                  norm_num [dusartPrimeRow_of_explicit_3802, dusartPrimeRow_of_explicit_right]

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_3275_3802_part02 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_3802 (p := 3331) (q := 3343) (by exact lowPrime_3343) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_3802 (p := 3343) (q := 3347) (by exact lowPrime_3347) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_3802 (p := 3347) (q := 3359) (by exact lowPrime_3359) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_3802 (p := 3359) (q := 3361) (by exact lowPrime_3361) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_3802 (p := 3361) (q := 3371) (by exact lowPrime_3371) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_3802 (p := 3371) (q := 3373) (by exact lowPrime_3373) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_3802 (p := 3373) (q := 3389) (by exact lowPrime_3389) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_3802 (p := 3389) (q := 3391) (by exact lowPrime_3391) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_3275_3802_part02_chain :
    DusartPrimeRowsChain 3331 3390 dusartPrimeRows_3275_3802_part02 := by
  apply DusartPrimeRowsChain.cons
  · norm_num [dusartPrimeRow_of_explicit_3802]
  · norm_num [dusartPrimeRow_of_explicit_3802]
  · apply DusartPrimeRowsChain.cons
    · norm_num [dusartPrimeRow_of_explicit_3802]
    · norm_num [dusartPrimeRow_of_explicit_3802]
    · apply DusartPrimeRowsChain.cons
      · norm_num [dusartPrimeRow_of_explicit_3802]
      · norm_num [dusartPrimeRow_of_explicit_3802]
      · apply DusartPrimeRowsChain.cons
        · norm_num [dusartPrimeRow_of_explicit_3802]
        · norm_num [dusartPrimeRow_of_explicit_3802]
        · apply DusartPrimeRowsChain.cons
          · norm_num [dusartPrimeRow_of_explicit_3802]
          · norm_num [dusartPrimeRow_of_explicit_3802]
          · apply DusartPrimeRowsChain.cons
            · norm_num [dusartPrimeRow_of_explicit_3802]
            · norm_num [dusartPrimeRow_of_explicit_3802]
            · apply DusartPrimeRowsChain.cons
              · norm_num [dusartPrimeRow_of_explicit_3802]
              · norm_num [dusartPrimeRow_of_explicit_3802]
              · apply DusartPrimeRowsChain.cons
                · norm_num [dusartPrimeRow_of_explicit_3802]
                · norm_num [dusartPrimeRow_of_explicit_3802]
                · apply DusartPrimeRowsChain.empty
                  norm_num [dusartPrimeRow_of_explicit_3802, dusartPrimeRow_of_explicit_right]

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_3275_3802_part03 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_3802 (p := 3391) (q := 3407) (by exact lowPrime_3407) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_3802 (p := 3407) (q := 3413) (by exact lowPrime_3413) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_3802 (p := 3413) (q := 3433) (by exact lowPrime_3433) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_3802 (p := 3433) (q := 3449) (by exact lowPrime_3449) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_3802 (p := 3449) (q := 3457) (by exact lowPrime_3457) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_3802 (p := 3457) (q := 3461) (by exact lowPrime_3461) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_3802 (p := 3461) (q := 3463) (by exact lowPrime_3463) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_3802 (p := 3463) (q := 3467) (by exact lowPrime_3467) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_3275_3802_part03_chain :
    DusartPrimeRowsChain 3391 3466 dusartPrimeRows_3275_3802_part03 := by
  apply DusartPrimeRowsChain.cons
  · norm_num [dusartPrimeRow_of_explicit_3802]
  · norm_num [dusartPrimeRow_of_explicit_3802]
  · apply DusartPrimeRowsChain.cons
    · norm_num [dusartPrimeRow_of_explicit_3802]
    · norm_num [dusartPrimeRow_of_explicit_3802]
    · apply DusartPrimeRowsChain.cons
      · norm_num [dusartPrimeRow_of_explicit_3802]
      · norm_num [dusartPrimeRow_of_explicit_3802]
      · apply DusartPrimeRowsChain.cons
        · norm_num [dusartPrimeRow_of_explicit_3802]
        · norm_num [dusartPrimeRow_of_explicit_3802]
        · apply DusartPrimeRowsChain.cons
          · norm_num [dusartPrimeRow_of_explicit_3802]
          · norm_num [dusartPrimeRow_of_explicit_3802]
          · apply DusartPrimeRowsChain.cons
            · norm_num [dusartPrimeRow_of_explicit_3802]
            · norm_num [dusartPrimeRow_of_explicit_3802]
            · apply DusartPrimeRowsChain.cons
              · norm_num [dusartPrimeRow_of_explicit_3802]
              · norm_num [dusartPrimeRow_of_explicit_3802]
              · apply DusartPrimeRowsChain.cons
                · norm_num [dusartPrimeRow_of_explicit_3802]
                · norm_num [dusartPrimeRow_of_explicit_3802]
                · apply DusartPrimeRowsChain.empty
                  norm_num [dusartPrimeRow_of_explicit_3802, dusartPrimeRow_of_explicit_right]

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_3275_3802_part04 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_3802 (p := 3467) (q := 3469) (by exact lowPrime_3469) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_3802 (p := 3469) (q := 3491) (by exact lowPrime_3491) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_3802 (p := 3491) (q := 3499) (by exact lowPrime_3499) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_3802 (p := 3499) (q := 3511) (by exact lowPrime_3511) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_3802 (p := 3511) (q := 3517) (by exact lowPrime_3517) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_3802 (p := 3517) (q := 3527) (by exact lowPrime_3527) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_3802 (p := 3527) (q := 3529) (by exact lowPrime_3529) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_3802 (p := 3529) (q := 3533) (by exact lowPrime_3533) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_3275_3802_part04_chain :
    DusartPrimeRowsChain 3467 3532 dusartPrimeRows_3275_3802_part04 := by
  apply DusartPrimeRowsChain.cons
  · norm_num [dusartPrimeRow_of_explicit_3802]
  · norm_num [dusartPrimeRow_of_explicit_3802]
  · apply DusartPrimeRowsChain.cons
    · norm_num [dusartPrimeRow_of_explicit_3802]
    · norm_num [dusartPrimeRow_of_explicit_3802]
    · apply DusartPrimeRowsChain.cons
      · norm_num [dusartPrimeRow_of_explicit_3802]
      · norm_num [dusartPrimeRow_of_explicit_3802]
      · apply DusartPrimeRowsChain.cons
        · norm_num [dusartPrimeRow_of_explicit_3802]
        · norm_num [dusartPrimeRow_of_explicit_3802]
        · apply DusartPrimeRowsChain.cons
          · norm_num [dusartPrimeRow_of_explicit_3802]
          · norm_num [dusartPrimeRow_of_explicit_3802]
          · apply DusartPrimeRowsChain.cons
            · norm_num [dusartPrimeRow_of_explicit_3802]
            · norm_num [dusartPrimeRow_of_explicit_3802]
            · apply DusartPrimeRowsChain.cons
              · norm_num [dusartPrimeRow_of_explicit_3802]
              · norm_num [dusartPrimeRow_of_explicit_3802]
              · apply DusartPrimeRowsChain.cons
                · norm_num [dusartPrimeRow_of_explicit_3802]
                · norm_num [dusartPrimeRow_of_explicit_3802]
                · apply DusartPrimeRowsChain.empty
                  norm_num [dusartPrimeRow_of_explicit_3802, dusartPrimeRow_of_explicit_right]

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_3275_3802_part05 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_3802 (p := 3533) (q := 3539) (by exact lowPrime_3539) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_3802 (p := 3539) (q := 3541) (by exact lowPrime_3541) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_3802 (p := 3541) (q := 3547) (by exact lowPrime_3547) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_3802 (p := 3547) (q := 3557) (by exact lowPrime_3557) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_3802 (p := 3557) (q := 3559) (by exact lowPrime_3559) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_3802 (p := 3559) (q := 3571) (by exact lowPrime_3571) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_3802 (p := 3571) (q := 3581) (by exact lowPrime_3581) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_3802 (p := 3581) (q := 3583) (by exact lowPrime_3583) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_3275_3802_part05_chain :
    DusartPrimeRowsChain 3533 3582 dusartPrimeRows_3275_3802_part05 := by
  apply DusartPrimeRowsChain.cons
  · norm_num [dusartPrimeRow_of_explicit_3802]
  · norm_num [dusartPrimeRow_of_explicit_3802]
  · apply DusartPrimeRowsChain.cons
    · norm_num [dusartPrimeRow_of_explicit_3802]
    · norm_num [dusartPrimeRow_of_explicit_3802]
    · apply DusartPrimeRowsChain.cons
      · norm_num [dusartPrimeRow_of_explicit_3802]
      · norm_num [dusartPrimeRow_of_explicit_3802]
      · apply DusartPrimeRowsChain.cons
        · norm_num [dusartPrimeRow_of_explicit_3802]
        · norm_num [dusartPrimeRow_of_explicit_3802]
        · apply DusartPrimeRowsChain.cons
          · norm_num [dusartPrimeRow_of_explicit_3802]
          · norm_num [dusartPrimeRow_of_explicit_3802]
          · apply DusartPrimeRowsChain.cons
            · norm_num [dusartPrimeRow_of_explicit_3802]
            · norm_num [dusartPrimeRow_of_explicit_3802]
            · apply DusartPrimeRowsChain.cons
              · norm_num [dusartPrimeRow_of_explicit_3802]
              · norm_num [dusartPrimeRow_of_explicit_3802]
              · apply DusartPrimeRowsChain.cons
                · norm_num [dusartPrimeRow_of_explicit_3802]
                · norm_num [dusartPrimeRow_of_explicit_3802]
                · apply DusartPrimeRowsChain.empty
                  norm_num [dusartPrimeRow_of_explicit_3802, dusartPrimeRow_of_explicit_right]

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_3275_3802_part06 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_3802 (p := 3583) (q := 3593) (by exact lowPrime_3593) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_3802 (p := 3593) (q := 3607) (by exact lowPrime_3607) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_3802 (p := 3607) (q := 3613) (by exact lowPrime_3613) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_3802 (p := 3613) (q := 3617) (by exact lowPrime_3617) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_3802 (p := 3617) (q := 3623) (by exact lowPrime_3623) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_3802 (p := 3623) (q := 3631) (by exact lowPrime_3631) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_3802 (p := 3631) (q := 3637) (by exact lowPrime_3637) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_3802 (p := 3637) (q := 3643) (by exact lowPrime_3643) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_3275_3802_part06_chain :
    DusartPrimeRowsChain 3583 3642 dusartPrimeRows_3275_3802_part06 := by
  apply DusartPrimeRowsChain.cons
  · norm_num [dusartPrimeRow_of_explicit_3802]
  · norm_num [dusartPrimeRow_of_explicit_3802]
  · apply DusartPrimeRowsChain.cons
    · norm_num [dusartPrimeRow_of_explicit_3802]
    · norm_num [dusartPrimeRow_of_explicit_3802]
    · apply DusartPrimeRowsChain.cons
      · norm_num [dusartPrimeRow_of_explicit_3802]
      · norm_num [dusartPrimeRow_of_explicit_3802]
      · apply DusartPrimeRowsChain.cons
        · norm_num [dusartPrimeRow_of_explicit_3802]
        · norm_num [dusartPrimeRow_of_explicit_3802]
        · apply DusartPrimeRowsChain.cons
          · norm_num [dusartPrimeRow_of_explicit_3802]
          · norm_num [dusartPrimeRow_of_explicit_3802]
          · apply DusartPrimeRowsChain.cons
            · norm_num [dusartPrimeRow_of_explicit_3802]
            · norm_num [dusartPrimeRow_of_explicit_3802]
            · apply DusartPrimeRowsChain.cons
              · norm_num [dusartPrimeRow_of_explicit_3802]
              · norm_num [dusartPrimeRow_of_explicit_3802]
              · apply DusartPrimeRowsChain.cons
                · norm_num [dusartPrimeRow_of_explicit_3802]
                · norm_num [dusartPrimeRow_of_explicit_3802]
                · apply DusartPrimeRowsChain.empty
                  norm_num [dusartPrimeRow_of_explicit_3802, dusartPrimeRow_of_explicit_right]

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_3275_3802_part07 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_3802 (p := 3643) (q := 3659) (by exact lowPrime_3659) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_3802 (p := 3659) (q := 3671) (by exact lowPrime_3671) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_3802 (p := 3671) (q := 3673) (by exact lowPrime_3673) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_3802 (p := 3673) (q := 3677) (by exact lowPrime_3677) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_3802 (p := 3677) (q := 3691) (by exact lowPrime_3691) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_3802 (p := 3691) (q := 3697) (by exact lowPrime_3697) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_3802 (p := 3697) (q := 3701) (by exact lowPrime_3701) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_3802 (p := 3701) (q := 3709) (by exact lowPrime_3709) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_3275_3802_part07_chain :
    DusartPrimeRowsChain 3643 3708 dusartPrimeRows_3275_3802_part07 := by
  apply DusartPrimeRowsChain.cons
  · norm_num [dusartPrimeRow_of_explicit_3802]
  · norm_num [dusartPrimeRow_of_explicit_3802]
  · apply DusartPrimeRowsChain.cons
    · norm_num [dusartPrimeRow_of_explicit_3802]
    · norm_num [dusartPrimeRow_of_explicit_3802]
    · apply DusartPrimeRowsChain.cons
      · norm_num [dusartPrimeRow_of_explicit_3802]
      · norm_num [dusartPrimeRow_of_explicit_3802]
      · apply DusartPrimeRowsChain.cons
        · norm_num [dusartPrimeRow_of_explicit_3802]
        · norm_num [dusartPrimeRow_of_explicit_3802]
        · apply DusartPrimeRowsChain.cons
          · norm_num [dusartPrimeRow_of_explicit_3802]
          · norm_num [dusartPrimeRow_of_explicit_3802]
          · apply DusartPrimeRowsChain.cons
            · norm_num [dusartPrimeRow_of_explicit_3802]
            · norm_num [dusartPrimeRow_of_explicit_3802]
            · apply DusartPrimeRowsChain.cons
              · norm_num [dusartPrimeRow_of_explicit_3802]
              · norm_num [dusartPrimeRow_of_explicit_3802]
              · apply DusartPrimeRowsChain.cons
                · norm_num [dusartPrimeRow_of_explicit_3802]
                · norm_num [dusartPrimeRow_of_explicit_3802]
                · apply DusartPrimeRowsChain.empty
                  norm_num [dusartPrimeRow_of_explicit_3802, dusartPrimeRow_of_explicit_right]

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_3275_3802_part08 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_3802 (p := 3709) (q := 3719) (by exact lowPrime_3719) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_3802 (p := 3719) (q := 3727) (by exact lowPrime_3727) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_3802 (p := 3727) (q := 3733) (by exact lowPrime_3733) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_3802 (p := 3733) (q := 3739) (by exact lowPrime_3739) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_3802 (p := 3739) (q := 3761) (by exact lowPrime_3761) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_3802 (p := 3761) (q := 3767) (by exact lowPrime_3767) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_3802 (p := 3767) (q := 3769) (by exact lowPrime_3769) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_3802 (p := 3769) (q := 3779) (by exact lowPrime_3779) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_3275_3802_part08_chain :
    DusartPrimeRowsChain 3709 3778 dusartPrimeRows_3275_3802_part08 := by
  apply DusartPrimeRowsChain.cons
  · norm_num [dusartPrimeRow_of_explicit_3802]
  · norm_num [dusartPrimeRow_of_explicit_3802]
  · apply DusartPrimeRowsChain.cons
    · norm_num [dusartPrimeRow_of_explicit_3802]
    · norm_num [dusartPrimeRow_of_explicit_3802]
    · apply DusartPrimeRowsChain.cons
      · norm_num [dusartPrimeRow_of_explicit_3802]
      · norm_num [dusartPrimeRow_of_explicit_3802]
      · apply DusartPrimeRowsChain.cons
        · norm_num [dusartPrimeRow_of_explicit_3802]
        · norm_num [dusartPrimeRow_of_explicit_3802]
        · apply DusartPrimeRowsChain.cons
          · norm_num [dusartPrimeRow_of_explicit_3802]
          · norm_num [dusartPrimeRow_of_explicit_3802]
          · apply DusartPrimeRowsChain.cons
            · norm_num [dusartPrimeRow_of_explicit_3802]
            · norm_num [dusartPrimeRow_of_explicit_3802]
            · apply DusartPrimeRowsChain.cons
              · norm_num [dusartPrimeRow_of_explicit_3802]
              · norm_num [dusartPrimeRow_of_explicit_3802]
              · apply DusartPrimeRowsChain.cons
                · norm_num [dusartPrimeRow_of_explicit_3802]
                · norm_num [dusartPrimeRow_of_explicit_3802]
                · apply DusartPrimeRowsChain.empty
                  norm_num [dusartPrimeRow_of_explicit_3802, dusartPrimeRow_of_explicit_right]

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_3275_3802_part09 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_3802 (p := 3779) (q := 3793) (by exact lowPrime_3793) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_3802 (p := 3793) (q := 3797) (by exact lowPrime_3797) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_3802 (p := 3797) (q := 3803) (by exact lowPrime_3803) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_3275_3802_part09_chain :
    DusartPrimeRowsChain 3779 3802 dusartPrimeRows_3275_3802_part09 := by
  apply DusartPrimeRowsChain.cons
  · norm_num [dusartPrimeRow_of_explicit_3802]
  · norm_num [dusartPrimeRow_of_explicit_3802]
  · apply DusartPrimeRowsChain.cons
    · norm_num [dusartPrimeRow_of_explicit_3802]
    · norm_num [dusartPrimeRow_of_explicit_3802]
    · apply DusartPrimeRowsChain.cons
      · norm_num [dusartPrimeRow_of_explicit_3802]
      · norm_num [dusartPrimeRow_of_explicit_3802]
      · apply DusartPrimeRowsChain.empty
        norm_num [dusartPrimeRow_of_explicit_3802, dusartPrimeRow_of_explicit_right]

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_3803_4672_part01 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_4670 (p := 3803) (q := 3821) (by exact lowPrime_3821) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_4670 (p := 3821) (q := 3823) (by exact lowPrime_3823) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_4670 (p := 3823) (q := 3833) (by exact lowPrime_3833) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_4670 (p := 3833) (q := 3847) (by exact lowPrime_3847) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_4670 (p := 3847) (q := 3851) (by exact lowPrime_3851) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_4670 (p := 3851) (q := 3853) (by exact lowPrime_3853) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_4670 (p := 3853) (q := 3863) (by exact lowPrime_3863) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_4670 (p := 3863) (q := 3877) (by exact lowPrime_3877) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_3803_4672_part01_chain :
    DusartPrimeRowsChain 3803 3876 dusartPrimeRows_3803_4672_part01 := by
  apply DusartPrimeRowsChain.cons
  · norm_num [dusartPrimeRow_of_explicit_4670]
  · norm_num [dusartPrimeRow_of_explicit_4670]
  · apply DusartPrimeRowsChain.cons
    · norm_num [dusartPrimeRow_of_explicit_4670]
    · norm_num [dusartPrimeRow_of_explicit_4670]
    · apply DusartPrimeRowsChain.cons
      · norm_num [dusartPrimeRow_of_explicit_4670]
      · norm_num [dusartPrimeRow_of_explicit_4670]
      · apply DusartPrimeRowsChain.cons
        · norm_num [dusartPrimeRow_of_explicit_4670]
        · norm_num [dusartPrimeRow_of_explicit_4670]
        · apply DusartPrimeRowsChain.cons
          · norm_num [dusartPrimeRow_of_explicit_4670]
          · norm_num [dusartPrimeRow_of_explicit_4670]
          · apply DusartPrimeRowsChain.cons
            · norm_num [dusartPrimeRow_of_explicit_4670]
            · norm_num [dusartPrimeRow_of_explicit_4670]
            · apply DusartPrimeRowsChain.cons
              · norm_num [dusartPrimeRow_of_explicit_4670]
              · norm_num [dusartPrimeRow_of_explicit_4670]
              · apply DusartPrimeRowsChain.cons
                · norm_num [dusartPrimeRow_of_explicit_4670]
                · norm_num [dusartPrimeRow_of_explicit_4670]
                · apply DusartPrimeRowsChain.empty
                  norm_num [dusartPrimeRow_of_explicit_4670, dusartPrimeRow_of_explicit_right]

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_3803_4672_part02 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_4670 (p := 3877) (q := 3881) (by exact lowPrime_3881) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_4670 (p := 3881) (q := 3889) (by exact lowPrime_3889) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_4670 (p := 3889) (q := 3907) (by exact lowPrime_3907) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_4670 (p := 3907) (q := 3911) (by exact lowPrime_3911) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_4670 (p := 3911) (q := 3917) (by exact lowPrime_3917) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_4670 (p := 3917) (q := 3919) (by exact lowPrime_3919) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_4670 (p := 3919) (q := 3923) (by exact lowPrime_3923) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_4670 (p := 3923) (q := 3929) (by exact lowPrime_3929) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_3803_4672_part02_chain :
    DusartPrimeRowsChain 3877 3928 dusartPrimeRows_3803_4672_part02 := by
  apply DusartPrimeRowsChain.cons
  · norm_num [dusartPrimeRow_of_explicit_4670]
  · norm_num [dusartPrimeRow_of_explicit_4670]
  · apply DusartPrimeRowsChain.cons
    · norm_num [dusartPrimeRow_of_explicit_4670]
    · norm_num [dusartPrimeRow_of_explicit_4670]
    · apply DusartPrimeRowsChain.cons
      · norm_num [dusartPrimeRow_of_explicit_4670]
      · norm_num [dusartPrimeRow_of_explicit_4670]
      · apply DusartPrimeRowsChain.cons
        · norm_num [dusartPrimeRow_of_explicit_4670]
        · norm_num [dusartPrimeRow_of_explicit_4670]
        · apply DusartPrimeRowsChain.cons
          · norm_num [dusartPrimeRow_of_explicit_4670]
          · norm_num [dusartPrimeRow_of_explicit_4670]
          · apply DusartPrimeRowsChain.cons
            · norm_num [dusartPrimeRow_of_explicit_4670]
            · norm_num [dusartPrimeRow_of_explicit_4670]
            · apply DusartPrimeRowsChain.cons
              · norm_num [dusartPrimeRow_of_explicit_4670]
              · norm_num [dusartPrimeRow_of_explicit_4670]
              · apply DusartPrimeRowsChain.cons
                · norm_num [dusartPrimeRow_of_explicit_4670]
                · norm_num [dusartPrimeRow_of_explicit_4670]
                · apply DusartPrimeRowsChain.empty
                  norm_num [dusartPrimeRow_of_explicit_4670, dusartPrimeRow_of_explicit_right]

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_3803_4672_part03 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_4670 (p := 3929) (q := 3931) (by exact lowPrime_3931) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_4670 (p := 3931) (q := 3943) (by exact lowPrime_3943) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_4670 (p := 3943) (q := 3947) (by exact lowPrime_3947) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_4670 (p := 3947) (q := 3967) (by exact lowPrime_3967) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_4670 (p := 3967) (q := 3989) (by exact lowPrime_3989) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_4670 (p := 3989) (q := 4001) (by exact lowPrime_4001) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_4670 (p := 4001) (q := 4003) (by exact lowPrime_4003) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_4670 (p := 4003) (q := 4007) (by exact lowPrime_4007) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_3803_4672_part03_chain :
    DusartPrimeRowsChain 3929 4006 dusartPrimeRows_3803_4672_part03 := by
  apply DusartPrimeRowsChain.cons
  · norm_num [dusartPrimeRow_of_explicit_4670]
  · norm_num [dusartPrimeRow_of_explicit_4670]
  · apply DusartPrimeRowsChain.cons
    · norm_num [dusartPrimeRow_of_explicit_4670]
    · norm_num [dusartPrimeRow_of_explicit_4670]
    · apply DusartPrimeRowsChain.cons
      · norm_num [dusartPrimeRow_of_explicit_4670]
      · norm_num [dusartPrimeRow_of_explicit_4670]
      · apply DusartPrimeRowsChain.cons
        · norm_num [dusartPrimeRow_of_explicit_4670]
        · norm_num [dusartPrimeRow_of_explicit_4670]
        · apply DusartPrimeRowsChain.cons
          · norm_num [dusartPrimeRow_of_explicit_4670]
          · norm_num [dusartPrimeRow_of_explicit_4670]
          · apply DusartPrimeRowsChain.cons
            · norm_num [dusartPrimeRow_of_explicit_4670]
            · norm_num [dusartPrimeRow_of_explicit_4670]
            · apply DusartPrimeRowsChain.cons
              · norm_num [dusartPrimeRow_of_explicit_4670]
              · norm_num [dusartPrimeRow_of_explicit_4670]
              · apply DusartPrimeRowsChain.cons
                · norm_num [dusartPrimeRow_of_explicit_4670]
                · norm_num [dusartPrimeRow_of_explicit_4670]
                · apply DusartPrimeRowsChain.empty
                  norm_num [dusartPrimeRow_of_explicit_4670, dusartPrimeRow_of_explicit_right]
