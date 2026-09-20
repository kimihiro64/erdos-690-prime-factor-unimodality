import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowBase

set_option autoImplicit false
set_option maxRecDepth 1000000

/-! # Lower finite Dusart prefix chunk 06 -/

namespace PrimeFactorUnimodality

noncomputable section
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_7297 : Nat.Prime 7297 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 7297 7296 1 5 [2, 2, 2, 2, 2, 2, 2, 3, 19]
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
    · apply IsUnit.of_mul_eq_one (3648 : ZMod 7297)
      decide
    · apply IsUnit.of_mul_eq_one (6118 : ZMod 7297)
      decide
    · apply IsUnit.of_mul_eq_one (462 : ZMod 7297)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_7307 : Nat.Prime 7307 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 7307 7306 1 2 [2, 13, 281]
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
    · apply IsUnit.of_mul_eq_one (3653 : ZMod 7307)
      decide
    · apply IsUnit.of_mul_eq_one (1176 : ZMod 7307)
      decide
    · apply IsUnit.of_mul_eq_one (2960 : ZMod 7307)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_7309 : Nat.Prime 7309 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 7309 7308 1 6 [2, 2, 3, 3, 7, 29]
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
    · apply IsUnit.of_mul_eq_one (3654 : ZMod 7309)
      decide
    · apply IsUnit.of_mul_eq_one (1297 : ZMod 7309)
      decide
    · apply IsUnit.of_mul_eq_one (3846 : ZMod 7309)
      decide
    · apply IsUnit.of_mul_eq_one (5445 : ZMod 7309)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_7321 : Nat.Prime 7321 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 7321 7320 1 7 [2, 2, 2, 3, 5, 61]
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
    · apply IsUnit.of_mul_eq_one (3660 : ZMod 7321)
      decide
    · apply IsUnit.of_mul_eq_one (2337 : ZMod 7321)
      decide
    · apply IsUnit.of_mul_eq_one (3995 : ZMod 7321)
      decide
    · apply IsUnit.of_mul_eq_one (853 : ZMod 7321)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_7331 : Nat.Prime 7331 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 7331 7330 1 2 [2, 5, 733]
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
    · apply IsUnit.of_mul_eq_one (3665 : ZMod 7331)
      decide
    · apply IsUnit.of_mul_eq_one (5638 : ZMod 7331)
      decide
    · apply IsUnit.of_mul_eq_one (2458 : ZMod 7331)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_7333 : Nat.Prime 7333 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 7333 7332 1 6 [2, 2, 3, 13, 47]
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
    · apply IsUnit.of_mul_eq_one (3666 : ZMod 7333)
      decide
    · apply IsUnit.of_mul_eq_one (5909 : ZMod 7333)
      decide
    · apply IsUnit.of_mul_eq_one (2053 : ZMod 7333)
      decide
    · apply IsUnit.of_mul_eq_one (5179 : ZMod 7333)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_7349 : Nat.Prime 7349 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 7349 7348 1 2 [2, 2, 11, 167]
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
    · apply IsUnit.of_mul_eq_one (3674 : ZMod 7349)
      decide
    · apply IsUnit.of_mul_eq_one (4401 : ZMod 7349)
      decide
    · apply IsUnit.of_mul_eq_one (4288 : ZMod 7349)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_7351 : Nat.Prime 7351 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 7351 7350 1 6 [2, 3, 5, 5, 7, 7]
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
    · apply IsUnit.of_mul_eq_one (3675 : ZMod 7351)
      decide
    · apply IsUnit.of_mul_eq_one (7301 : ZMod 7351)
      decide
    · apply IsUnit.of_mul_eq_one (1681 : ZMod 7351)
      decide
    · apply IsUnit.of_mul_eq_one (562 : ZMod 7351)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_7369 : Nat.Prime 7369 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 7369 7368 1 7 [2, 2, 2, 3, 307]
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
    · apply IsUnit.of_mul_eq_one (3684 : ZMod 7369)
      decide
    · apply IsUnit.of_mul_eq_one (3309 : ZMod 7369)
      decide
    · apply IsUnit.of_mul_eq_one (4219 : ZMod 7369)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_7393 : Nat.Prime 7393 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 7393 7392 1 5 [2, 2, 2, 2, 2, 3, 7, 11]
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
    · apply IsUnit.of_mul_eq_one (3696 : ZMod 7393)
      decide
    · apply IsUnit.of_mul_eq_one (6820 : ZMod 7393)
      decide
    · apply IsUnit.of_mul_eq_one (4639 : ZMod 7393)
      decide
    · apply IsUnit.of_mul_eq_one (1531 : ZMod 7393)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_7411 : Nat.Prime 7411 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 7411 7410 1 2 [2, 3, 5, 13, 19]
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
    · apply IsUnit.of_mul_eq_one (3705 : ZMod 7411)
      decide
    · apply IsUnit.of_mul_eq_one (7279 : ZMod 7411)
      decide
    · apply IsUnit.of_mul_eq_one (6680 : ZMod 7411)
      decide
    · apply IsUnit.of_mul_eq_one (6714 : ZMod 7411)
      decide
    · apply IsUnit.of_mul_eq_one (6930 : ZMod 7411)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_7417 : Nat.Prime 7417 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 7417 7416 1 5 [2, 2, 2, 3, 3, 103]
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
    · apply IsUnit.of_mul_eq_one (3708 : ZMod 7417)
      decide
    · apply IsUnit.of_mul_eq_one (1701 : ZMod 7417)
      decide
    · apply IsUnit.of_mul_eq_one (6171 : ZMod 7417)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_7433 : Nat.Prime 7433 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 7433 7432 1 3 [2, 2, 2, 929]
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
    · apply IsUnit.of_mul_eq_one (3716 : ZMod 7433)
      decide
    · apply IsUnit.of_mul_eq_one (298 : ZMod 7433)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_7451 : Nat.Prime 7451 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 7451 7450 1 2 [2, 5, 5, 149]
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
    · apply IsUnit.of_mul_eq_one (3725 : ZMod 7451)
      decide
    · apply IsUnit.of_mul_eq_one (7046 : ZMod 7451)
      decide
    · apply IsUnit.of_mul_eq_one (1670 : ZMod 7451)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
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
  · decide
  · intro q hq
    simp at hq
    rcases hq with rfl | rfl
    · apply IsUnit.of_mul_eq_one (3728 : ZMod 7457)
      decide
    · apply IsUnit.of_mul_eq_one (4858 : ZMod 7457)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
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
  · decide
  · intro q hq
    simp at hq
    rcases hq with rfl | rfl | rfl | rfl
    · apply IsUnit.of_mul_eq_one (3729 : ZMod 7459)
      decide
    · apply IsUnit.of_mul_eq_one (2562 : ZMod 7459)
      decide
    · apply IsUnit.of_mul_eq_one (4094 : ZMod 7459)
      decide
    · apply IsUnit.of_mul_eq_one (5218 : ZMod 7459)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
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
  · decide
  · intro q hq
    simp at hq
    rcases hq with rfl | rfl | rfl | rfl
    · apply IsUnit.of_mul_eq_one (3738 : ZMod 7477)
      decide
    · apply IsUnit.of_mul_eq_one (3828 : ZMod 7477)
      decide
    · apply IsUnit.of_mul_eq_one (4413 : ZMod 7477)
      decide
    · apply IsUnit.of_mul_eq_one (2010 : ZMod 7477)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
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
  · decide
  · intro q hq
    simp at hq
    rcases hq with rfl | rfl | rfl | rfl
    · apply IsUnit.of_mul_eq_one (3740 : ZMod 7481)
      decide
    · apply IsUnit.of_mul_eq_one (1350 : ZMod 7481)
      decide
    · apply IsUnit.of_mul_eq_one (1129 : ZMod 7481)
      decide
    · apply IsUnit.of_mul_eq_one (2799 : ZMod 7481)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
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
  · decide
  · intro q hq
    simp at hq
    rcases hq with rfl | rfl | rfl
    · apply IsUnit.of_mul_eq_one (3743 : ZMod 7487)
      decide
    · apply IsUnit.of_mul_eq_one (794 : ZMod 7487)
      decide
    · apply IsUnit.of_mul_eq_one (2258 : ZMod 7487)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
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
  · decide
  · intro q hq
    simp at hq
    rcases hq with rfl | rfl | rfl
    · apply IsUnit.of_mul_eq_one (3744 : ZMod 7489)
      decide
    · apply IsUnit.of_mul_eq_one (822 : ZMod 7489)
      decide
    · apply IsUnit.of_mul_eq_one (7432 : ZMod 7489)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
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
  · decide
  · intro q hq
    simp at hq
    rcases hq with rfl | rfl | rfl
    · apply IsUnit.of_mul_eq_one (3749 : ZMod 7499)
      decide
    · apply IsUnit.of_mul_eq_one (1804 : ZMod 7499)
      decide
    · apply IsUnit.of_mul_eq_one (646 : ZMod 7499)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
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
  · decide
  · intro q hq
    simp at hq
    rcases hq with rfl | rfl | rfl
    · apply IsUnit.of_mul_eq_one (3753 : ZMod 7507)
      decide
    · apply IsUnit.of_mul_eq_one (4802 : ZMod 7507)
      decide
    · apply IsUnit.of_mul_eq_one (6606 : ZMod 7507)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_7517 : Nat.Prime 7517 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 7517 7516 1 2 [2, 2, 1879]
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
    · apply IsUnit.of_mul_eq_one (3758 : ZMod 7517)
      decide
    · apply IsUnit.of_mul_eq_one (3508 : ZMod 7517)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_7523 : Nat.Prime 7523 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 7523 7522 1 2 [2, 3761]
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
    · apply IsUnit.of_mul_eq_one (3761 : ZMod 7523)
      decide
    · apply IsUnit.of_mul_eq_one (2508 : ZMod 7523)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_7529 : Nat.Prime 7529 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 7529 7528 1 3 [2, 2, 2, 941]
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
    · apply IsUnit.of_mul_eq_one (3764 : ZMod 7529)
      decide
    · apply IsUnit.of_mul_eq_one (2836 : ZMod 7529)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_7537 : Nat.Prime 7537 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 7537 7536 1 7 [2, 2, 2, 2, 3, 157]
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
    · apply IsUnit.of_mul_eq_one (3768 : ZMod 7537)
      decide
    · apply IsUnit.of_mul_eq_one (4370 : ZMod 7537)
      decide
    · apply IsUnit.of_mul_eq_one (4862 : ZMod 7537)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_7541 : Nat.Prime 7541 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 7541 7540 1 2 [2, 2, 5, 13, 29]
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
    · apply IsUnit.of_mul_eq_one (3770 : ZMod 7541)
      decide
    · apply IsUnit.of_mul_eq_one (5508 : ZMod 7541)
      decide
    · apply IsUnit.of_mul_eq_one (227 : ZMod 7541)
      decide
    · apply IsUnit.of_mul_eq_one (6838 : ZMod 7541)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_7547 : Nat.Prime 7547 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 7547 7546 1 2 [2, 7, 7, 7, 11]
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
    · apply IsUnit.of_mul_eq_one (3773 : ZMod 7547)
      decide
    · apply IsUnit.of_mul_eq_one (7341 : ZMod 7547)
      decide
    · apply IsUnit.of_mul_eq_one (5352 : ZMod 7547)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_7549 : Nat.Prime 7549 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 7549 7548 1 2 [2, 2, 3, 17, 37]
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
    · apply IsUnit.of_mul_eq_one (3774 : ZMod 7549)
      decide
    · apply IsUnit.of_mul_eq_one (4856 : ZMod 7549)
      decide
    · apply IsUnit.of_mul_eq_one (2349 : ZMod 7549)
      decide
    · apply IsUnit.of_mul_eq_one (580 : ZMod 7549)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_7559 : Nat.Prime 7559 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 7559 7558 1 13 [2, 3779]
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
    · apply IsUnit.of_mul_eq_one (3779 : ZMod 7559)
      decide
    · apply IsUnit.of_mul_eq_one (45 : ZMod 7559)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_7561 : Nat.Prime 7561 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 7561 7560 1 13 [2, 2, 2, 3, 3, 3, 5, 7]
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
    · apply IsUnit.of_mul_eq_one (3780 : ZMod 7561)
      decide
    · apply IsUnit.of_mul_eq_one (2087 : ZMod 7561)
      decide
    · apply IsUnit.of_mul_eq_one (278 : ZMod 7561)
      decide
    · apply IsUnit.of_mul_eq_one (3561 : ZMod 7561)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_7573 : Nat.Prime 7573 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 7573 7572 1 2 [2, 2, 3, 631]
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
    · apply IsUnit.of_mul_eq_one (3786 : ZMod 7573)
      decide
    · apply IsUnit.of_mul_eq_one (5734 : ZMod 7573)
      decide
    · apply IsUnit.of_mul_eq_one (5646 : ZMod 7573)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_7577 : Nat.Prime 7577 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 7577 7576 1 3 [2, 2, 2, 947]
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
    · apply IsUnit.of_mul_eq_one (3788 : ZMod 7577)
      decide
    · apply IsUnit.of_mul_eq_one (4351 : ZMod 7577)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_7583 : Nat.Prime 7583 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 7583 7582 1 5 [2, 17, 223]
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
    · apply IsUnit.of_mul_eq_one (3791 : ZMod 7583)
      decide
    · apply IsUnit.of_mul_eq_one (1199 : ZMod 7583)
      decide
    · apply IsUnit.of_mul_eq_one (2873 : ZMod 7583)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_7589 : Nat.Prime 7589 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 7589 7588 1 2 [2, 2, 7, 271]
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
    · apply IsUnit.of_mul_eq_one (3794 : ZMod 7589)
      decide
    · apply IsUnit.of_mul_eq_one (4982 : ZMod 7589)
      decide
    · apply IsUnit.of_mul_eq_one (964 : ZMod 7589)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_7591 : Nat.Prime 7591 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 7591 7590 1 6 [2, 3, 5, 11, 23]
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
    · apply IsUnit.of_mul_eq_one (3795 : ZMod 7591)
      decide
    · apply IsUnit.of_mul_eq_one (5878 : ZMod 7591)
      decide
    · apply IsUnit.of_mul_eq_one (6259 : ZMod 7591)
      decide
    · apply IsUnit.of_mul_eq_one (5417 : ZMod 7591)
      decide
    · apply IsUnit.of_mul_eq_one (1949 : ZMod 7591)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_7603 : Nat.Prime 7603 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 7603 7602 1 2 [2, 3, 7, 181]
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
    · apply IsUnit.of_mul_eq_one (3801 : ZMod 7603)
      decide
    · apply IsUnit.of_mul_eq_one (3232 : ZMod 7603)
      decide
    · apply IsUnit.of_mul_eq_one (2473 : ZMod 7603)
      decide
    · apply IsUnit.of_mul_eq_one (255 : ZMod 7603)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_7607 : Nat.Prime 7607 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 7607 7606 1 5 [2, 3803]
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
    · apply IsUnit.of_mul_eq_one (3803 : ZMod 7607)
      decide
    · apply IsUnit.of_mul_eq_one (317 : ZMod 7607)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_7621 : Nat.Prime 7621 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 7621 7620 1 2 [2, 2, 3, 5, 127]
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
    · apply IsUnit.of_mul_eq_one (3810 : ZMod 7621)
      decide
    · apply IsUnit.of_mul_eq_one (6579 : ZMod 7621)
      decide
    · apply IsUnit.of_mul_eq_one (3611 : ZMod 7621)
      decide
    · apply IsUnit.of_mul_eq_one (597 : ZMod 7621)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_7639 : Nat.Prime 7639 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 7639 7638 1 7 [2, 3, 19, 67]
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
    · apply IsUnit.of_mul_eq_one (3819 : ZMod 7639)
      decide
    · apply IsUnit.of_mul_eq_one (1554 : ZMod 7639)
      decide
    · apply IsUnit.of_mul_eq_one (6711 : ZMod 7639)
      decide
    · apply IsUnit.of_mul_eq_one (7484 : ZMod 7639)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_7643 : Nat.Prime 7643 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 7643 7642 1 2 [2, 3821]
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
    · apply IsUnit.of_mul_eq_one (3821 : ZMod 7643)
      decide
    · apply IsUnit.of_mul_eq_one (2548 : ZMod 7643)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_7649 : Nat.Prime 7649 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 7649 7648 1 3 [2, 2, 2, 2, 2, 239]
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
    · apply IsUnit.of_mul_eq_one (3824 : ZMod 7649)
      decide
    · apply IsUnit.of_mul_eq_one (7552 : ZMod 7649)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_7669 : Nat.Prime 7669 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 7669 7668 1 2 [2, 2, 3, 3, 3, 71]
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
    · apply IsUnit.of_mul_eq_one (3834 : ZMod 7669)
      decide
    · apply IsUnit.of_mul_eq_one (3246 : ZMod 7669)
      decide
    · apply IsUnit.of_mul_eq_one (1530 : ZMod 7669)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_7673 : Nat.Prime 7673 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 7673 7672 1 3 [2, 2, 2, 7, 137]
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
    · apply IsUnit.of_mul_eq_one (3836 : ZMod 7673)
      decide
    · apply IsUnit.of_mul_eq_one (195 : ZMod 7673)
      decide
    · apply IsUnit.of_mul_eq_one (2222 : ZMod 7673)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_7681 : Nat.Prime 7681 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 7681 7680 1 17 [2, 2, 2, 2, 2, 2, 2, 2, 2, 3, 5]
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
    rcases hq with rfl | rfl | rfl
    · apply IsUnit.of_mul_eq_one (3840 : ZMod 7681)
      decide
    · apply IsUnit.of_mul_eq_one (4892 : ZMod 7681)
      decide
    · apply IsUnit.of_mul_eq_one (288 : ZMod 7681)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_7687 : Nat.Prime 7687 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 7687 7686 1 6 [2, 3, 3, 7, 61]
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
    · apply IsUnit.of_mul_eq_one (3843 : ZMod 7687)
      decide
    · apply IsUnit.of_mul_eq_one (4366 : ZMod 7687)
      decide
    · apply IsUnit.of_mul_eq_one (27 : ZMod 7687)
      decide
    · apply IsUnit.of_mul_eq_one (1642 : ZMod 7687)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_7691 : Nat.Prime 7691 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 7691 7690 1 2 [2, 5, 769]
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
    · apply IsUnit.of_mul_eq_one (3845 : ZMod 7691)
      decide
    · apply IsUnit.of_mul_eq_one (7630 : ZMod 7691)
      decide
    · apply IsUnit.of_mul_eq_one (7067 : ZMod 7691)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_7699 : Nat.Prime 7699 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 7699 7698 1 3 [2, 3, 1283]
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
    · apply IsUnit.of_mul_eq_one (3849 : ZMod 7699)
      decide
    · apply IsUnit.of_mul_eq_one (6942 : ZMod 7699)
      decide
    · apply IsUnit.of_mul_eq_one (6229 : ZMod 7699)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_7703 : Nat.Prime 7703 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 7703 7702 1 5 [2, 3851]
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
    · apply IsUnit.of_mul_eq_one (3851 : ZMod 7703)
      decide
    · apply IsUnit.of_mul_eq_one (321 : ZMod 7703)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_7717 : Nat.Prime 7717 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 7717 7716 1 2 [2, 2, 3, 643]
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
    · apply IsUnit.of_mul_eq_one (3858 : ZMod 7717)
      decide
    · apply IsUnit.of_mul_eq_one (1146 : ZMod 7717)
      decide
    · apply IsUnit.of_mul_eq_one (1191 : ZMod 7717)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_7723 : Nat.Prime 7723 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 7723 7722 1 3 [2, 3, 3, 3, 11, 13]
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
    · apply IsUnit.of_mul_eq_one (3861 : ZMod 7723)
      decide
    · apply IsUnit.of_mul_eq_one (2268 : ZMod 7723)
      decide
    · apply IsUnit.of_mul_eq_one (5436 : ZMod 7723)
      decide
    · apply IsUnit.of_mul_eq_one (2495 : ZMod 7723)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_7727 : Nat.Prime 7727 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 7727 7726 1 5 [2, 3863]
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
    · apply IsUnit.of_mul_eq_one (3863 : ZMod 7727)
      decide
    · apply IsUnit.of_mul_eq_one (322 : ZMod 7727)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_7741 : Nat.Prime 7741 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 7741 7740 1 7 [2, 2, 3, 3, 5, 43]
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
    · apply IsUnit.of_mul_eq_one (3870 : ZMod 7741)
      decide
    · apply IsUnit.of_mul_eq_one (6923 : ZMod 7741)
      decide
    · apply IsUnit.of_mul_eq_one (6692 : ZMod 7741)
      decide
    · apply IsUnit.of_mul_eq_one (6190 : ZMod 7741)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_7753 : Nat.Prime 7753 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 7753 7752 1 10 [2, 2, 2, 3, 17, 19]
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
    · apply IsUnit.of_mul_eq_one (3876 : ZMod 7753)
      decide
    · apply IsUnit.of_mul_eq_one (134 : ZMod 7753)
      decide
    · apply IsUnit.of_mul_eq_one (6588 : ZMod 7753)
      decide
    · apply IsUnit.of_mul_eq_one (276 : ZMod 7753)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_7757 : Nat.Prime 7757 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 7757 7756 1 2 [2, 2, 7, 277]
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
    · apply IsUnit.of_mul_eq_one (3878 : ZMod 7757)
      decide
    · apply IsUnit.of_mul_eq_one (3715 : ZMod 7757)
      decide
    · apply IsUnit.of_mul_eq_one (6780 : ZMod 7757)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_7759 : Nat.Prime 7759 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 7759 7758 1 3 [2, 3, 3, 431]
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
    · apply IsUnit.of_mul_eq_one (3879 : ZMod 7759)
      decide
    · apply IsUnit.of_mul_eq_one (586 : ZMod 7759)
      decide
    · apply IsUnit.of_mul_eq_one (976 : ZMod 7759)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_7789 : Nat.Prime 7789 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 7789 7788 1 2 [2, 2, 3, 11, 59]
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
    · apply IsUnit.of_mul_eq_one (3894 : ZMod 7789)
      decide
    · apply IsUnit.of_mul_eq_one (2518 : ZMod 7789)
      decide
    · apply IsUnit.of_mul_eq_one (5304 : ZMod 7789)
      decide
    · apply IsUnit.of_mul_eq_one (5307 : ZMod 7789)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_7793 : Nat.Prime 7793 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 7793 7792 1 3 [2, 2, 2, 2, 487]
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
    · apply IsUnit.of_mul_eq_one (3896 : ZMod 7793)
      decide
    · apply IsUnit.of_mul_eq_one (1673 : ZMod 7793)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_7817 : Nat.Prime 7817 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 7817 7816 1 3 [2, 2, 2, 977]
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
    · apply IsUnit.of_mul_eq_one (3908 : ZMod 7817)
      decide
    · apply IsUnit.of_mul_eq_one (199 : ZMod 7817)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_7823 : Nat.Prime 7823 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 7823 7822 1 5 [2, 3911]
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
    · apply IsUnit.of_mul_eq_one (3911 : ZMod 7823)
      decide
    · apply IsUnit.of_mul_eq_one (326 : ZMod 7823)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_7829 : Nat.Prime 7829 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 7829 7828 1 2 [2, 2, 19, 103]
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
    · apply IsUnit.of_mul_eq_one (3914 : ZMod 7829)
      decide
    · apply IsUnit.of_mul_eq_one (6811 : ZMod 7829)
      decide
    · apply IsUnit.of_mul_eq_one (2733 : ZMod 7829)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_7841 : Nat.Prime 7841 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 7841 7840 1 12 [2, 2, 2, 2, 2, 5, 7, 7]
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
    · apply IsUnit.of_mul_eq_one (3920 : ZMod 7841)
      decide
    · apply IsUnit.of_mul_eq_one (1195 : ZMod 7841)
      decide
    · apply IsUnit.of_mul_eq_one (2473 : ZMod 7841)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_7853 : Nat.Prime 7853 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 7853 7852 1 2 [2, 2, 13, 151]
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
    · apply IsUnit.of_mul_eq_one (3926 : ZMod 7853)
      decide
    · apply IsUnit.of_mul_eq_one (5013 : ZMod 7853)
      decide
    · apply IsUnit.of_mul_eq_one (5732 : ZMod 7853)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_7867 : Nat.Prime 7867 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 7867 7866 1 3 [2, 3, 3, 19, 23]
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
    · apply IsUnit.of_mul_eq_one (3933 : ZMod 7867)
      decide
    · apply IsUnit.of_mul_eq_one (7378 : ZMod 7867)
      decide
    · apply IsUnit.of_mul_eq_one (6739 : ZMod 7867)
      decide
    · apply IsUnit.of_mul_eq_one (5227 : ZMod 7867)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_7873 : Nat.Prime 7873 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 7873 7872 1 5 [2, 2, 2, 2, 2, 2, 3, 41]
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
    · apply IsUnit.of_mul_eq_one (3936 : ZMod 7873)
      decide
    · apply IsUnit.of_mul_eq_one (5713 : ZMod 7873)
      decide
    · apply IsUnit.of_mul_eq_one (4507 : ZMod 7873)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_7877 : Nat.Prime 7877 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 7877 7876 1 2 [2, 2, 11, 179]
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
    · apply IsUnit.of_mul_eq_one (3938 : ZMod 7877)
      decide
    · apply IsUnit.of_mul_eq_one (4769 : ZMod 7877)
      decide
    · apply IsUnit.of_mul_eq_one (5211 : ZMod 7877)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_7879 : Nat.Prime 7879 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 7879 7878 1 3 [2, 3, 13, 101]
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
    · apply IsUnit.of_mul_eq_one (3939 : ZMod 7879)
      decide
    · apply IsUnit.of_mul_eq_one (7423 : ZMod 7879)
      decide
    · apply IsUnit.of_mul_eq_one (1076 : ZMod 7879)
      decide
    · apply IsUnit.of_mul_eq_one (4802 : ZMod 7879)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_7883 : Nat.Prime 7883 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 7883 7882 1 2 [2, 7, 563]
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
    · apply IsUnit.of_mul_eq_one (3941 : ZMod 7883)
      decide
    · apply IsUnit.of_mul_eq_one (7597 : ZMod 7883)
      decide
    · apply IsUnit.of_mul_eq_one (6912 : ZMod 7883)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_7901 : Nat.Prime 7901 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 7901 7900 1 2 [2, 2, 5, 5, 79]
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
    · apply IsUnit.of_mul_eq_one (3950 : ZMod 7901)
      decide
    · apply IsUnit.of_mul_eq_one (4943 : ZMod 7901)
      decide
    · apply IsUnit.of_mul_eq_one (92 : ZMod 7901)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_7907 : Nat.Prime 7907 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 7907 7906 1 2 [2, 59, 67]
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
    · apply IsUnit.of_mul_eq_one (3953 : ZMod 7907)
      decide
    · apply IsUnit.of_mul_eq_one (3922 : ZMod 7907)
      decide
    · apply IsUnit.of_mul_eq_one (813 : ZMod 7907)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_7919 : Nat.Prime 7919 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 7919 7918 1 7 [2, 37, 107]
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
    · apply IsUnit.of_mul_eq_one (3959 : ZMod 7919)
      decide
    · apply IsUnit.of_mul_eq_one (5934 : ZMod 7919)
      decide
    · apply IsUnit.of_mul_eq_one (3370 : ZMod 7919)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_7927 : Nat.Prime 7927 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 7927 7926 1 3 [2, 3, 1321]
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
    · apply IsUnit.of_mul_eq_one (3963 : ZMod 7927)
      decide
    · apply IsUnit.of_mul_eq_one (3895 : ZMod 7927)
      decide
    · apply IsUnit.of_mul_eq_one (98 : ZMod 7927)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_7933 : Nat.Prime 7933 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 7933 7932 1 2 [2, 2, 3, 661]
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
    · apply IsUnit.of_mul_eq_one (3966 : ZMod 7933)
      decide
    · apply IsUnit.of_mul_eq_one (668 : ZMod 7933)
      decide
    · apply IsUnit.of_mul_eq_one (3735 : ZMod 7933)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_7937 : Nat.Prime 7937 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 7937 7936 1 3 [2, 2, 2, 2, 2, 2, 2, 2, 31]
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
    · apply IsUnit.of_mul_eq_one (3968 : ZMod 7937)
      decide
    · apply IsUnit.of_mul_eq_one (4154 : ZMod 7937)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_7949 : Nat.Prime 7949 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 7949 7948 1 2 [2, 2, 1987]
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
    · apply IsUnit.of_mul_eq_one (3974 : ZMod 7949)
      decide
    · apply IsUnit.of_mul_eq_one (530 : ZMod 7949)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_7951 : Nat.Prime 7951 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 7951 7950 1 6 [2, 3, 5, 5, 53]
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
    · apply IsUnit.of_mul_eq_one (3975 : ZMod 7951)
      decide
    · apply IsUnit.of_mul_eq_one (2757 : ZMod 7951)
      decide
    · apply IsUnit.of_mul_eq_one (1845 : ZMod 7951)
      decide
    · apply IsUnit.of_mul_eq_one (54 : ZMod 7951)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_7963 : Nat.Prime 7963 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 7963 7962 1 5 [2, 3, 1327]
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
    · apply IsUnit.of_mul_eq_one (3981 : ZMod 7963)
      decide
    · apply IsUnit.of_mul_eq_one (4767 : ZMod 7963)
      decide
    · apply IsUnit.of_mul_eq_one (3085 : ZMod 7963)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_7993 : Nat.Prime 7993 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 7993 7992 1 5 [2, 2, 2, 3, 3, 3, 37]
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
    · apply IsUnit.of_mul_eq_one (3996 : ZMod 7993)
      decide
    · apply IsUnit.of_mul_eq_one (1081 : ZMod 7993)
      decide
    · apply IsUnit.of_mul_eq_one (6551 : ZMod 7993)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_8009 : Nat.Prime 8009 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 8009 8008 1 3 [2, 2, 2, 7, 11, 13]
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
    · apply IsUnit.of_mul_eq_one (4004 : ZMod 8009)
      decide
    · apply IsUnit.of_mul_eq_one (6638 : ZMod 8009)
      decide
    · apply IsUnit.of_mul_eq_one (7070 : ZMod 8009)
      decide
    · apply IsUnit.of_mul_eq_one (5524 : ZMod 8009)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_8011 : Nat.Prime 8011 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 8011 8010 1 14 [2, 3, 3, 5, 89]
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
    · apply IsUnit.of_mul_eq_one (4005 : ZMod 8011)
      decide
    · apply IsUnit.of_mul_eq_one (5370 : ZMod 8011)
      decide
    · apply IsUnit.of_mul_eq_one (1854 : ZMod 8011)
      decide
    · apply IsUnit.of_mul_eq_one (5977 : ZMod 8011)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_8017 : Nat.Prime 8017 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 8017 8016 1 5 [2, 2, 2, 2, 3, 167]
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
    · apply IsUnit.of_mul_eq_one (4008 : ZMod 8017)
      decide
    · apply IsUnit.of_mul_eq_one (6225 : ZMod 8017)
      decide
    · apply IsUnit.of_mul_eq_one (5098 : ZMod 8017)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_8039 : Nat.Prime 8039 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 8039 8038 1 11 [2, 4019]
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
    · apply IsUnit.of_mul_eq_one (4019 : ZMod 8039)
      decide
    · apply IsUnit.of_mul_eq_one (67 : ZMod 8039)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_8053 : Nat.Prime 8053 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 8053 8052 1 2 [2, 2, 3, 11, 61]
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
    · apply IsUnit.of_mul_eq_one (4026 : ZMod 8053)
      decide
    · apply IsUnit.of_mul_eq_one (1518 : ZMod 8053)
      decide
    · apply IsUnit.of_mul_eq_one (1992 : ZMod 8053)
      decide
    · apply IsUnit.of_mul_eq_one (5193 : ZMod 8053)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_8059 : Nat.Prime 8059 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 8059 8058 1 3 [2, 3, 17, 79]
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
    · apply IsUnit.of_mul_eq_one (4029 : ZMod 8059)
      decide
    · apply IsUnit.of_mul_eq_one (6294 : ZMod 8059)
      decide
    · apply IsUnit.of_mul_eq_one (254 : ZMod 8059)
      decide
    · apply IsUnit.of_mul_eq_one (4922 : ZMod 8059)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_8069 : Nat.Prime 8069 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 8069 8068 1 2 [2, 2, 2017]
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
    · apply IsUnit.of_mul_eq_one (4034 : ZMod 8069)
      decide
    · apply IsUnit.of_mul_eq_one (538 : ZMod 8069)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_8081 : Nat.Prime 8081 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 8081 8080 1 3 [2, 2, 2, 2, 5, 101]
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
    · apply IsUnit.of_mul_eq_one (4040 : ZMod 8081)
      decide
    · apply IsUnit.of_mul_eq_one (1879 : ZMod 8081)
      decide
    · apply IsUnit.of_mul_eq_one (4940 : ZMod 8081)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_8087 : Nat.Prime 8087 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 8087 8086 1 5 [2, 13, 311]
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
    · apply IsUnit.of_mul_eq_one (4043 : ZMod 8087)
      decide
    · apply IsUnit.of_mul_eq_one (1618 : ZMod 8087)
      decide
    · apply IsUnit.of_mul_eq_one (2827 : ZMod 8087)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_8089 : Nat.Prime 8089 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 8089 8088 1 17 [2, 2, 2, 3, 337]
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
    · apply IsUnit.of_mul_eq_one (4044 : ZMod 8089)
      decide
    · apply IsUnit.of_mul_eq_one (3167 : ZMod 8089)
      decide
    · apply IsUnit.of_mul_eq_one (2666 : ZMod 8089)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_8093 : Nat.Prime 8093 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 8093 8092 1 2 [2, 2, 7, 17, 17]
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
    · apply IsUnit.of_mul_eq_one (4046 : ZMod 8093)
      decide
    · apply IsUnit.of_mul_eq_one (636 : ZMod 8093)
      decide
    · apply IsUnit.of_mul_eq_one (4863 : ZMod 8093)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_8101 : Nat.Prime 8101 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 8101 8100 1 6 [2, 2, 3, 3, 3, 3, 5, 5]
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
    · apply IsUnit.of_mul_eq_one (4050 : ZMod 8101)
      decide
    · apply IsUnit.of_mul_eq_one (3439 : ZMod 8101)
      decide
    · apply IsUnit.of_mul_eq_one (2794 : ZMod 8101)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_8111 : Nat.Prime 8111 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 8111 8110 1 11 [2, 5, 811]
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
    · apply IsUnit.of_mul_eq_one (4055 : ZMod 8111)
      decide
    · apply IsUnit.of_mul_eq_one (7491 : ZMod 8111)
      decide
    · apply IsUnit.of_mul_eq_one (3137 : ZMod 8111)
      decide
  · norm_num
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_6977_7332_part05 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_7331 (p := 7283) (q := 7297) (by exact lowPrime_7297) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_7331 (p := 7297) (q := 7307) (by exact lowPrime_7307) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_7331 (p := 7307) (q := 7309) (by exact lowPrime_7309) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_7331 (p := 7309) (q := 7321) (by exact lowPrime_7321) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_7331 (p := 7321) (q := 7331) (by exact lowPrime_7331) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_7331 (p := 7331) (q := 7333) (by exact lowPrime_7333) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_6977_7332_part05_chain :
    DusartPrimeRowsChain 7283 7332 dusartPrimeRows_6977_7332_part05 := by
  apply DusartPrimeRowsChain.cons
  · norm_num [dusartPrimeRow_of_explicit_7331]
  · norm_num [dusartPrimeRow_of_explicit_7331]
  · apply DusartPrimeRowsChain.cons
    · norm_num [dusartPrimeRow_of_explicit_7331]
    · norm_num [dusartPrimeRow_of_explicit_7331]
    · apply DusartPrimeRowsChain.cons
      · norm_num [dusartPrimeRow_of_explicit_7331]
      · norm_num [dusartPrimeRow_of_explicit_7331]
      · apply DusartPrimeRowsChain.cons
        · norm_num [dusartPrimeRow_of_explicit_7331]
        · norm_num [dusartPrimeRow_of_explicit_7331]
        · apply DusartPrimeRowsChain.cons
          · norm_num [dusartPrimeRow_of_explicit_7331]
          · norm_num [dusartPrimeRow_of_explicit_7331]
          · apply DusartPrimeRowsChain.cons
            · norm_num [dusartPrimeRow_of_explicit_7331]
            · norm_num [dusartPrimeRow_of_explicit_7331]
            · apply DusartPrimeRowsChain.empty
              norm_num [dusartPrimeRow_of_explicit_7331, dusartPrimeRow_of_explicit_right]

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_7333_7716_part01 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_7707 (p := 7333) (q := 7349) (by exact lowPrime_7349) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_7707 (p := 7349) (q := 7351) (by exact lowPrime_7351) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_7707 (p := 7351) (q := 7369) (by exact lowPrime_7369) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_7707 (p := 7369) (q := 7393) (by exact lowPrime_7393) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_7707 (p := 7393) (q := 7411) (by exact lowPrime_7411) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_7707 (p := 7411) (q := 7417) (by exact lowPrime_7417) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_7707 (p := 7417) (q := 7433) (by exact lowPrime_7433) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_7707 (p := 7433) (q := 7451) (by exact lowPrime_7451) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_7333_7716_part01_chain :
    DusartPrimeRowsChain 7333 7450 dusartPrimeRows_7333_7716_part01 := by
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
                  norm_num [dusartPrimeRow_of_explicit_7707, dusartPrimeRow_of_explicit_right]

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
    DusartPrimeRowsChain 7451 7506 dusartPrimeRows_7333_7716_part02 := by
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
                  norm_num [dusartPrimeRow_of_explicit_7707, dusartPrimeRow_of_explicit_right]

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_7333_7716_part03 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_7707 (p := 7507) (q := 7517) (by exact lowPrime_7517) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_7707 (p := 7517) (q := 7523) (by exact lowPrime_7523) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_7707 (p := 7523) (q := 7529) (by exact lowPrime_7529) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_7707 (p := 7529) (q := 7537) (by exact lowPrime_7537) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_7707 (p := 7537) (q := 7541) (by exact lowPrime_7541) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_7707 (p := 7541) (q := 7547) (by exact lowPrime_7547) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_7707 (p := 7547) (q := 7549) (by exact lowPrime_7549) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_7707 (p := 7549) (q := 7559) (by exact lowPrime_7559) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_7333_7716_part03_chain :
    DusartPrimeRowsChain 7507 7558 dusartPrimeRows_7333_7716_part03 := by
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
                  norm_num [dusartPrimeRow_of_explicit_7707, dusartPrimeRow_of_explicit_right]

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_7333_7716_part04 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_7707 (p := 7559) (q := 7561) (by exact lowPrime_7561) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_7707 (p := 7561) (q := 7573) (by exact lowPrime_7573) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_7707 (p := 7573) (q := 7577) (by exact lowPrime_7577) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_7707 (p := 7577) (q := 7583) (by exact lowPrime_7583) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_7707 (p := 7583) (q := 7589) (by exact lowPrime_7589) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_7707 (p := 7589) (q := 7591) (by exact lowPrime_7591) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_7707 (p := 7591) (q := 7603) (by exact lowPrime_7603) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_7707 (p := 7603) (q := 7607) (by exact lowPrime_7607) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_7333_7716_part04_chain :
    DusartPrimeRowsChain 7559 7606 dusartPrimeRows_7333_7716_part04 := by
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
                  norm_num [dusartPrimeRow_of_explicit_7707, dusartPrimeRow_of_explicit_right]

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_7333_7716_part05 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_7707 (p := 7607) (q := 7621) (by exact lowPrime_7621) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_7707 (p := 7621) (q := 7639) (by exact lowPrime_7639) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_7707 (p := 7639) (q := 7643) (by exact lowPrime_7643) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_7707 (p := 7643) (q := 7649) (by exact lowPrime_7649) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_7707 (p := 7649) (q := 7669) (by exact lowPrime_7669) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_7707 (p := 7669) (q := 7673) (by exact lowPrime_7673) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_7707 (p := 7673) (q := 7681) (by exact lowPrime_7681) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_7707 (p := 7681) (q := 7687) (by exact lowPrime_7687) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_7333_7716_part05_chain :
    DusartPrimeRowsChain 7607 7686 dusartPrimeRows_7333_7716_part05 := by
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
                  norm_num [dusartPrimeRow_of_explicit_7707, dusartPrimeRow_of_explicit_right]

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_7333_7716_part06 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_7707 (p := 7687) (q := 7691) (by exact lowPrime_7691) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_7707 (p := 7691) (q := 7699) (by exact lowPrime_7699) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_7707 (p := 7699) (q := 7703) (by exact lowPrime_7703) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_7707 (p := 7703) (q := 7717) (by exact lowPrime_7717) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_7333_7716_part06_chain :
    DusartPrimeRowsChain 7687 7716 dusartPrimeRows_7333_7716_part06 := by
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
        · apply DusartPrimeRowsChain.empty
          norm_num [dusartPrimeRow_of_explicit_7707, dusartPrimeRow_of_explicit_right]

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_7717_8110_part01 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_8103 (p := 7717) (q := 7723) (by exact lowPrime_7723) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8103 (p := 7723) (q := 7727) (by exact lowPrime_7727) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8103 (p := 7727) (q := 7741) (by exact lowPrime_7741) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8103 (p := 7741) (q := 7753) (by exact lowPrime_7753) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8103 (p := 7753) (q := 7757) (by exact lowPrime_7757) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8103 (p := 7757) (q := 7759) (by exact lowPrime_7759) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8103 (p := 7759) (q := 7789) (by exact lowPrime_7789) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8103 (p := 7789) (q := 7793) (by exact lowPrime_7793) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_7717_8110_part01_chain :
    DusartPrimeRowsChain 7717 7792 dusartPrimeRows_7717_8110_part01 := by
  apply DusartPrimeRowsChain.cons
  · norm_num [dusartPrimeRow_of_explicit_8103]
  · norm_num [dusartPrimeRow_of_explicit_8103]
  · apply DusartPrimeRowsChain.cons
    · norm_num [dusartPrimeRow_of_explicit_8103]
    · norm_num [dusartPrimeRow_of_explicit_8103]
    · apply DusartPrimeRowsChain.cons
      · norm_num [dusartPrimeRow_of_explicit_8103]
      · norm_num [dusartPrimeRow_of_explicit_8103]
      · apply DusartPrimeRowsChain.cons
        · norm_num [dusartPrimeRow_of_explicit_8103]
        · norm_num [dusartPrimeRow_of_explicit_8103]
        · apply DusartPrimeRowsChain.cons
          · norm_num [dusartPrimeRow_of_explicit_8103]
          · norm_num [dusartPrimeRow_of_explicit_8103]
          · apply DusartPrimeRowsChain.cons
            · norm_num [dusartPrimeRow_of_explicit_8103]
            · norm_num [dusartPrimeRow_of_explicit_8103]
            · apply DusartPrimeRowsChain.cons
              · norm_num [dusartPrimeRow_of_explicit_8103]
              · norm_num [dusartPrimeRow_of_explicit_8103]
              · apply DusartPrimeRowsChain.cons
                · norm_num [dusartPrimeRow_of_explicit_8103]
                · norm_num [dusartPrimeRow_of_explicit_8103]
                · apply DusartPrimeRowsChain.empty
                  norm_num [dusartPrimeRow_of_explicit_8103, dusartPrimeRow_of_explicit_right]

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_7717_8110_part02 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_8103 (p := 7793) (q := 7817) (by exact lowPrime_7817) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8103 (p := 7817) (q := 7823) (by exact lowPrime_7823) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8103 (p := 7823) (q := 7829) (by exact lowPrime_7829) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8103 (p := 7829) (q := 7841) (by exact lowPrime_7841) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8103 (p := 7841) (q := 7853) (by exact lowPrime_7853) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8103 (p := 7853) (q := 7867) (by exact lowPrime_7867) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8103 (p := 7867) (q := 7873) (by exact lowPrime_7873) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8103 (p := 7873) (q := 7877) (by exact lowPrime_7877) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_7717_8110_part02_chain :
    DusartPrimeRowsChain 7793 7876 dusartPrimeRows_7717_8110_part02 := by
  apply DusartPrimeRowsChain.cons
  · norm_num [dusartPrimeRow_of_explicit_8103]
  · norm_num [dusartPrimeRow_of_explicit_8103]
  · apply DusartPrimeRowsChain.cons
    · norm_num [dusartPrimeRow_of_explicit_8103]
    · norm_num [dusartPrimeRow_of_explicit_8103]
    · apply DusartPrimeRowsChain.cons
      · norm_num [dusartPrimeRow_of_explicit_8103]
      · norm_num [dusartPrimeRow_of_explicit_8103]
      · apply DusartPrimeRowsChain.cons
        · norm_num [dusartPrimeRow_of_explicit_8103]
        · norm_num [dusartPrimeRow_of_explicit_8103]
        · apply DusartPrimeRowsChain.cons
          · norm_num [dusartPrimeRow_of_explicit_8103]
          · norm_num [dusartPrimeRow_of_explicit_8103]
          · apply DusartPrimeRowsChain.cons
            · norm_num [dusartPrimeRow_of_explicit_8103]
            · norm_num [dusartPrimeRow_of_explicit_8103]
            · apply DusartPrimeRowsChain.cons
              · norm_num [dusartPrimeRow_of_explicit_8103]
              · norm_num [dusartPrimeRow_of_explicit_8103]
              · apply DusartPrimeRowsChain.cons
                · norm_num [dusartPrimeRow_of_explicit_8103]
                · norm_num [dusartPrimeRow_of_explicit_8103]
                · apply DusartPrimeRowsChain.empty
                  norm_num [dusartPrimeRow_of_explicit_8103, dusartPrimeRow_of_explicit_right]

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_7717_8110_part03 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_8103 (p := 7877) (q := 7879) (by exact lowPrime_7879) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8103 (p := 7879) (q := 7883) (by exact lowPrime_7883) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8103 (p := 7883) (q := 7901) (by exact lowPrime_7901) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8103 (p := 7901) (q := 7907) (by exact lowPrime_7907) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8103 (p := 7907) (q := 7919) (by exact lowPrime_7919) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8103 (p := 7919) (q := 7927) (by exact lowPrime_7927) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8103 (p := 7927) (q := 7933) (by exact lowPrime_7933) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8103 (p := 7933) (q := 7937) (by exact lowPrime_7937) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_7717_8110_part03_chain :
    DusartPrimeRowsChain 7877 7936 dusartPrimeRows_7717_8110_part03 := by
  apply DusartPrimeRowsChain.cons
  · norm_num [dusartPrimeRow_of_explicit_8103]
  · norm_num [dusartPrimeRow_of_explicit_8103]
  · apply DusartPrimeRowsChain.cons
    · norm_num [dusartPrimeRow_of_explicit_8103]
    · norm_num [dusartPrimeRow_of_explicit_8103]
    · apply DusartPrimeRowsChain.cons
      · norm_num [dusartPrimeRow_of_explicit_8103]
      · norm_num [dusartPrimeRow_of_explicit_8103]
      · apply DusartPrimeRowsChain.cons
        · norm_num [dusartPrimeRow_of_explicit_8103]
        · norm_num [dusartPrimeRow_of_explicit_8103]
        · apply DusartPrimeRowsChain.cons
          · norm_num [dusartPrimeRow_of_explicit_8103]
          · norm_num [dusartPrimeRow_of_explicit_8103]
          · apply DusartPrimeRowsChain.cons
            · norm_num [dusartPrimeRow_of_explicit_8103]
            · norm_num [dusartPrimeRow_of_explicit_8103]
            · apply DusartPrimeRowsChain.cons
              · norm_num [dusartPrimeRow_of_explicit_8103]
              · norm_num [dusartPrimeRow_of_explicit_8103]
              · apply DusartPrimeRowsChain.cons
                · norm_num [dusartPrimeRow_of_explicit_8103]
                · norm_num [dusartPrimeRow_of_explicit_8103]
                · apply DusartPrimeRowsChain.empty
                  norm_num [dusartPrimeRow_of_explicit_8103, dusartPrimeRow_of_explicit_right]

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_7717_8110_part04 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_8103 (p := 7937) (q := 7949) (by exact lowPrime_7949) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8103 (p := 7949) (q := 7951) (by exact lowPrime_7951) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8103 (p := 7951) (q := 7963) (by exact lowPrime_7963) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8103 (p := 7963) (q := 7993) (by exact lowPrime_7993) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8103 (p := 7993) (q := 8009) (by exact lowPrime_8009) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8103 (p := 8009) (q := 8011) (by exact lowPrime_8011) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8103 (p := 8011) (q := 8017) (by exact lowPrime_8017) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8103 (p := 8017) (q := 8039) (by exact lowPrime_8039) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_7717_8110_part04_chain :
    DusartPrimeRowsChain 7937 8038 dusartPrimeRows_7717_8110_part04 := by
  apply DusartPrimeRowsChain.cons
  · norm_num [dusartPrimeRow_of_explicit_8103]
  · norm_num [dusartPrimeRow_of_explicit_8103]
  · apply DusartPrimeRowsChain.cons
    · norm_num [dusartPrimeRow_of_explicit_8103]
    · norm_num [dusartPrimeRow_of_explicit_8103]
    · apply DusartPrimeRowsChain.cons
      · norm_num [dusartPrimeRow_of_explicit_8103]
      · norm_num [dusartPrimeRow_of_explicit_8103]
      · apply DusartPrimeRowsChain.cons
        · norm_num [dusartPrimeRow_of_explicit_8103]
        · norm_num [dusartPrimeRow_of_explicit_8103]
        · apply DusartPrimeRowsChain.cons
          · norm_num [dusartPrimeRow_of_explicit_8103]
          · norm_num [dusartPrimeRow_of_explicit_8103]
          · apply DusartPrimeRowsChain.cons
            · norm_num [dusartPrimeRow_of_explicit_8103]
            · norm_num [dusartPrimeRow_of_explicit_8103]
            · apply DusartPrimeRowsChain.cons
              · norm_num [dusartPrimeRow_of_explicit_8103]
              · norm_num [dusartPrimeRow_of_explicit_8103]
              · apply DusartPrimeRowsChain.cons
                · norm_num [dusartPrimeRow_of_explicit_8103]
                · norm_num [dusartPrimeRow_of_explicit_8103]
                · apply DusartPrimeRowsChain.empty
                  norm_num [dusartPrimeRow_of_explicit_8103, dusartPrimeRow_of_explicit_right]

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_7717_8110_part05 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_8103 (p := 8039) (q := 8053) (by exact lowPrime_8053) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8103 (p := 8053) (q := 8059) (by exact lowPrime_8059) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8103 (p := 8059) (q := 8069) (by exact lowPrime_8069) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8103 (p := 8069) (q := 8081) (by exact lowPrime_8081) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8103 (p := 8081) (q := 8087) (by exact lowPrime_8087) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8103 (p := 8087) (q := 8089) (by exact lowPrime_8089) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8103 (p := 8089) (q := 8093) (by exact lowPrime_8093) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8103 (p := 8093) (q := 8101) (by exact lowPrime_8101) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_7717_8110_part05_chain :
    DusartPrimeRowsChain 8039 8100 dusartPrimeRows_7717_8110_part05 := by
  apply DusartPrimeRowsChain.cons
  · norm_num [dusartPrimeRow_of_explicit_8103]
  · norm_num [dusartPrimeRow_of_explicit_8103]
  · apply DusartPrimeRowsChain.cons
    · norm_num [dusartPrimeRow_of_explicit_8103]
    · norm_num [dusartPrimeRow_of_explicit_8103]
    · apply DusartPrimeRowsChain.cons
      · norm_num [dusartPrimeRow_of_explicit_8103]
      · norm_num [dusartPrimeRow_of_explicit_8103]
      · apply DusartPrimeRowsChain.cons
        · norm_num [dusartPrimeRow_of_explicit_8103]
        · norm_num [dusartPrimeRow_of_explicit_8103]
        · apply DusartPrimeRowsChain.cons
          · norm_num [dusartPrimeRow_of_explicit_8103]
          · norm_num [dusartPrimeRow_of_explicit_8103]
          · apply DusartPrimeRowsChain.cons
            · norm_num [dusartPrimeRow_of_explicit_8103]
            · norm_num [dusartPrimeRow_of_explicit_8103]
            · apply DusartPrimeRowsChain.cons
              · norm_num [dusartPrimeRow_of_explicit_8103]
              · norm_num [dusartPrimeRow_of_explicit_8103]
              · apply DusartPrimeRowsChain.cons
                · norm_num [dusartPrimeRow_of_explicit_8103]
                · norm_num [dusartPrimeRow_of_explicit_8103]
                · apply DusartPrimeRowsChain.empty
                  norm_num [dusartPrimeRow_of_explicit_8103, dusartPrimeRow_of_explicit_right]

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_7717_8110_part06 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_8103 (p := 8101) (q := 8111) (by exact lowPrime_8111) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_7717_8110_part06_chain :
    DusartPrimeRowsChain 8101 8110 dusartPrimeRows_7717_8110_part06 := by
  apply DusartPrimeRowsChain.cons
  · norm_num [dusartPrimeRow_of_explicit_8103]
  · norm_num [dusartPrimeRow_of_explicit_8103]
  · apply DusartPrimeRowsChain.empty
    norm_num [dusartPrimeRow_of_explicit_8103, dusartPrimeRow_of_explicit_right]
