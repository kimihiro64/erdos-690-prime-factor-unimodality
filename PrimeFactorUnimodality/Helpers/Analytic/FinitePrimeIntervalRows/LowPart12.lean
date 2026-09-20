import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowBase

set_option autoImplicit false
set_option maxRecDepth 1000000

/-! # Lower finite Dusart prefix chunk 12 -/

namespace PrimeFactorUnimodality

noncomputable section
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_12401 : Nat.Prime 12401 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 12401 12400 1 3 [2, 2, 2, 2, 5, 5, 31]
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
    · apply IsUnit.of_mul_eq_one (6200 : ZMod 12401)
      decide
    · apply IsUnit.of_mul_eq_one (6547 : ZMod 12401)
      decide
    · apply IsUnit.of_mul_eq_one (4992 : ZMod 12401)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_12409 : Nat.Prime 12409 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 12409 12408 1 7 [2, 2, 2, 3, 11, 47]
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
    · apply IsUnit.of_mul_eq_one (6204 : ZMod 12409)
      decide
    · apply IsUnit.of_mul_eq_one (5073 : ZMod 12409)
      decide
    · apply IsUnit.of_mul_eq_one (2225 : ZMod 12409)
      decide
    · apply IsUnit.of_mul_eq_one (7159 : ZMod 12409)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_12413 : Nat.Prime 12413 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 12413 12412 1 2 [2, 2, 29, 107]
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
    · apply IsUnit.of_mul_eq_one (6206 : ZMod 12413)
      decide
    · apply IsUnit.of_mul_eq_one (10094 : ZMod 12413)
      decide
    · apply IsUnit.of_mul_eq_one (12056 : ZMod 12413)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_12421 : Nat.Prime 12421 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 12421 12420 1 7 [2, 2, 3, 3, 3, 5, 23]
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
    · apply IsUnit.of_mul_eq_one (6210 : ZMod 12421)
      decide
    · apply IsUnit.of_mul_eq_one (6094 : ZMod 12421)
      decide
    · apply IsUnit.of_mul_eq_one (2768 : ZMod 12421)
      decide
    · apply IsUnit.of_mul_eq_one (11217 : ZMod 12421)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_12433 : Nat.Prime 12433 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 12433 12432 1 13 [2, 2, 2, 2, 3, 7, 37]
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
    · apply IsUnit.of_mul_eq_one (6216 : ZMod 12433)
      decide
    · apply IsUnit.of_mul_eq_one (4181 : ZMod 12433)
      decide
    · apply IsUnit.of_mul_eq_one (1734 : ZMod 12433)
      decide
    · apply IsUnit.of_mul_eq_one (1838 : ZMod 12433)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_12437 : Nat.Prime 12437 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 12437 12436 1 2 [2, 2, 3109]
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
    · apply IsUnit.of_mul_eq_one (6218 : ZMod 12437)
      decide
    · apply IsUnit.of_mul_eq_one (5804 : ZMod 12437)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_12451 : Nat.Prime 12451 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 12451 12450 1 3 [2, 3, 5, 5, 83]
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
    · apply IsUnit.of_mul_eq_one (6225 : ZMod 12451)
      decide
    · apply IsUnit.of_mul_eq_one (11613 : ZMod 12451)
      decide
    · apply IsUnit.of_mul_eq_one (4657 : ZMod 12451)
      decide
    · apply IsUnit.of_mul_eq_one (10897 : ZMod 12451)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_12457 : Nat.Prime 12457 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 12457 12456 1 10 [2, 2, 2, 3, 3, 173]
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
    · apply IsUnit.of_mul_eq_one (6228 : ZMod 12457)
      decide
    · apply IsUnit.of_mul_eq_one (8142 : ZMod 12457)
      decide
    · apply IsUnit.of_mul_eq_one (11299 : ZMod 12457)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_12473 : Nat.Prime 12473 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 12473 12472 1 3 [2, 2, 2, 1559]
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
    · apply IsUnit.of_mul_eq_one (6236 : ZMod 12473)
      decide
    · apply IsUnit.of_mul_eq_one (7345 : ZMod 12473)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_12479 : Nat.Prime 12479 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 12479 12478 1 23 [2, 17, 367]
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
    · apply IsUnit.of_mul_eq_one (6239 : ZMod 12479)
      decide
    · apply IsUnit.of_mul_eq_one (149 : ZMod 12479)
      decide
    · apply IsUnit.of_mul_eq_one (9801 : ZMod 12479)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_12487 : Nat.Prime 12487 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 12487 12486 1 3 [2, 3, 2081]
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
    · apply IsUnit.of_mul_eq_one (6243 : ZMod 12487)
      decide
    · apply IsUnit.of_mul_eq_one (2484 : ZMod 12487)
      decide
    · apply IsUnit.of_mul_eq_one (8662 : ZMod 12487)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_12491 : Nat.Prime 12491 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 12491 12490 1 2 [2, 5, 1249]
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
    · apply IsUnit.of_mul_eq_one (6245 : ZMod 12491)
      decide
    · apply IsUnit.of_mul_eq_one (9723 : ZMod 12491)
      decide
    · apply IsUnit.of_mul_eq_one (3602 : ZMod 12491)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_12497 : Nat.Prime 12497 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 12497 12496 1 3 [2, 2, 2, 2, 11, 71]
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
    · apply IsUnit.of_mul_eq_one (6248 : ZMod 12497)
      decide
    · apply IsUnit.of_mul_eq_one (1844 : ZMod 12497)
      decide
    · apply IsUnit.of_mul_eq_one (459 : ZMod 12497)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_12503 : Nat.Prime 12503 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 12503 12502 1 5 [2, 7, 19, 47]
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
    · apply IsUnit.of_mul_eq_one (6251 : ZMod 12503)
      decide
    · apply IsUnit.of_mul_eq_one (10651 : ZMod 12503)
      decide
    · apply IsUnit.of_mul_eq_one (11847 : ZMod 12503)
      decide
    · apply IsUnit.of_mul_eq_one (1457 : ZMod 12503)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_12511 : Nat.Prime 12511 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 12511 12510 1 3 [2, 3, 3, 5, 139]
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
    · apply IsUnit.of_mul_eq_one (6255 : ZMod 12511)
      decide
    · apply IsUnit.of_mul_eq_one (1131 : ZMod 12511)
      decide
    · apply IsUnit.of_mul_eq_one (4449 : ZMod 12511)
      decide
    · apply IsUnit.of_mul_eq_one (6900 : ZMod 12511)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_12517 : Nat.Prime 12517 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 12517 12516 1 6 [2, 2, 3, 7, 149]
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
    · apply IsUnit.of_mul_eq_one (6258 : ZMod 12517)
      decide
    · apply IsUnit.of_mul_eq_one (10381 : ZMod 12517)
      decide
    · apply IsUnit.of_mul_eq_one (9433 : ZMod 12517)
      decide
    · apply IsUnit.of_mul_eq_one (10602 : ZMod 12517)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_12527 : Nat.Prime 12527 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 12527 12526 1 5 [2, 6263]
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
    · apply IsUnit.of_mul_eq_one (6263 : ZMod 12527)
      decide
    · apply IsUnit.of_mul_eq_one (522 : ZMod 12527)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_12539 : Nat.Prime 12539 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 12539 12538 1 2 [2, 6269]
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
    · apply IsUnit.of_mul_eq_one (6269 : ZMod 12539)
      decide
    · apply IsUnit.of_mul_eq_one (4180 : ZMod 12539)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_12541 : Nat.Prime 12541 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 12541 12540 1 14 [2, 2, 3, 5, 11, 19]
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
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · apply IsUnit.of_mul_eq_one (6270 : ZMod 12541)
      decide
    · apply IsUnit.of_mul_eq_one (794 : ZMod 12541)
      decide
    · apply IsUnit.of_mul_eq_one (9909 : ZMod 12541)
      decide
    · apply IsUnit.of_mul_eq_one (11141 : ZMod 12541)
      decide
    · apply IsUnit.of_mul_eq_one (3226 : ZMod 12541)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_12547 : Nat.Prime 12547 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 12547 12546 1 2 [2, 3, 3, 17, 41]
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
    · apply IsUnit.of_mul_eq_one (6273 : ZMod 12547)
      decide
    · apply IsUnit.of_mul_eq_one (10474 : ZMod 12547)
      decide
    · apply IsUnit.of_mul_eq_one (10732 : ZMod 12547)
      decide
    · apply IsUnit.of_mul_eq_one (2315 : ZMod 12547)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_12553 : Nat.Prime 12553 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 12553 12552 1 5 [2, 2, 2, 3, 523]
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
    · apply IsUnit.of_mul_eq_one (6276 : ZMod 12553)
      decide
    · apply IsUnit.of_mul_eq_one (6649 : ZMod 12553)
      decide
    · apply IsUnit.of_mul_eq_one (8792 : ZMod 12553)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_12569 : Nat.Prime 12569 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 12569 12568 1 3 [2, 2, 2, 1571]
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
    · apply IsUnit.of_mul_eq_one (6284 : ZMod 12569)
      decide
    · apply IsUnit.of_mul_eq_one (1209 : ZMod 12569)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_12577 : Nat.Prime 12577 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 12577 12576 1 10 [2, 2, 2, 2, 2, 3, 131]
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
    · apply IsUnit.of_mul_eq_one (6288 : ZMod 12577)
      decide
    · apply IsUnit.of_mul_eq_one (9989 : ZMod 12577)
      decide
    · apply IsUnit.of_mul_eq_one (286 : ZMod 12577)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_12583 : Nat.Prime 12583 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 12583 12582 1 5 [2, 3, 3, 3, 233]
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
    · apply IsUnit.of_mul_eq_one (6291 : ZMod 12583)
      decide
    · apply IsUnit.of_mul_eq_one (3628 : ZMod 12583)
      decide
    · apply IsUnit.of_mul_eq_one (3258 : ZMod 12583)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_12589 : Nat.Prime 12589 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 12589 12588 1 2 [2, 2, 3, 1049]
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
    · apply IsUnit.of_mul_eq_one (6294 : ZMod 12589)
      decide
    · apply IsUnit.of_mul_eq_one (5975 : ZMod 12589)
      decide
    · apply IsUnit.of_mul_eq_one (11885 : ZMod 12589)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_12601 : Nat.Prime 12601 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 12601 12600 1 11 [2, 2, 2, 3, 3, 5, 5, 7]
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
    · apply IsUnit.of_mul_eq_one (6300 : ZMod 12601)
      decide
    · apply IsUnit.of_mul_eq_one (282 : ZMod 12601)
      decide
    · apply IsUnit.of_mul_eq_one (11301 : ZMod 12601)
      decide
    · apply IsUnit.of_mul_eq_one (10631 : ZMod 12601)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_12611 : Nat.Prime 12611 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 12611 12610 1 2 [2, 5, 13, 97]
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
    · apply IsUnit.of_mul_eq_one (6305 : ZMod 12611)
      decide
    · apply IsUnit.of_mul_eq_one (5112 : ZMod 12611)
      decide
    · apply IsUnit.of_mul_eq_one (7453 : ZMod 12611)
      decide
    · apply IsUnit.of_mul_eq_one (7749 : ZMod 12611)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_12613 : Nat.Prime 12613 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 12613 12612 1 2 [2, 2, 3, 1051]
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
    · apply IsUnit.of_mul_eq_one (6306 : ZMod 12613)
      decide
    · apply IsUnit.of_mul_eq_one (6029 : ZMod 12613)
      decide
    · apply IsUnit.of_mul_eq_one (11344 : ZMod 12613)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_12619 : Nat.Prime 12619 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 12619 12618 1 2 [2, 3, 3, 701]
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
    · apply IsUnit.of_mul_eq_one (6309 : ZMod 12619)
      decide
    · apply IsUnit.of_mul_eq_one (5464 : ZMod 12619)
      decide
    · apply IsUnit.of_mul_eq_one (2735 : ZMod 12619)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_12637 : Nat.Prime 12637 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 12637 12636 1 2 [2, 2, 3, 3, 3, 3, 3, 13]
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
    · apply IsUnit.of_mul_eq_one (6318 : ZMod 12637)
      decide
    · apply IsUnit.of_mul_eq_one (2024 : ZMod 12637)
      decide
    · apply IsUnit.of_mul_eq_one (8630 : ZMod 12637)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_12641 : Nat.Prime 12641 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 12641 12640 1 3 [2, 2, 2, 2, 2, 5, 79]
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
    · apply IsUnit.of_mul_eq_one (6320 : ZMod 12641)
      decide
    · apply IsUnit.of_mul_eq_one (3382 : ZMod 12641)
      decide
    · apply IsUnit.of_mul_eq_one (1581 : ZMod 12641)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_12647 : Nat.Prime 12647 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 12647 12646 1 5 [2, 6323]
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
    · apply IsUnit.of_mul_eq_one (6323 : ZMod 12647)
      decide
    · apply IsUnit.of_mul_eq_one (527 : ZMod 12647)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_12653 : Nat.Prime 12653 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 12653 12652 1 2 [2, 2, 3163]
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
    · apply IsUnit.of_mul_eq_one (6326 : ZMod 12653)
      decide
    · apply IsUnit.of_mul_eq_one (10966 : ZMod 12653)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_12659 : Nat.Prime 12659 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 12659 12658 1 2 [2, 6329]
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
    · apply IsUnit.of_mul_eq_one (6329 : ZMod 12659)
      decide
    · apply IsUnit.of_mul_eq_one (4220 : ZMod 12659)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_12671 : Nat.Prime 12671 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 12671 12670 1 14 [2, 5, 7, 181]
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
    · apply IsUnit.of_mul_eq_one (6335 : ZMod 12671)
      decide
    · apply IsUnit.of_mul_eq_one (5372 : ZMod 12671)
      decide
    · apply IsUnit.of_mul_eq_one (9543 : ZMod 12671)
      decide
    · apply IsUnit.of_mul_eq_one (4836 : ZMod 12671)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_12689 : Nat.Prime 12689 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 12689 12688 1 3 [2, 2, 2, 2, 13, 61]
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
    · apply IsUnit.of_mul_eq_one (6344 : ZMod 12689)
      decide
    · apply IsUnit.of_mul_eq_one (11382 : ZMod 12689)
      decide
    · apply IsUnit.of_mul_eq_one (11571 : ZMod 12689)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_12697 : Nat.Prime 12697 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 12697 12696 1 7 [2, 2, 2, 3, 23, 23]
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
    · apply IsUnit.of_mul_eq_one (6348 : ZMod 12697)
      decide
    · apply IsUnit.of_mul_eq_one (8031 : ZMod 12697)
      decide
    · apply IsUnit.of_mul_eq_one (3721 : ZMod 12697)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_12703 : Nat.Prime 12703 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 12703 12702 1 3 [2, 3, 29, 73]
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
    · apply IsUnit.of_mul_eq_one (6351 : ZMod 12703)
      decide
    · apply IsUnit.of_mul_eq_one (2449 : ZMod 12703)
      decide
    · apply IsUnit.of_mul_eq_one (9325 : ZMod 12703)
      decide
    · apply IsUnit.of_mul_eq_one (9787 : ZMod 12703)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_12713 : Nat.Prime 12713 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 12713 12712 1 3 [2, 2, 2, 7, 227]
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
    · apply IsUnit.of_mul_eq_one (6356 : ZMod 12713)
      decide
    · apply IsUnit.of_mul_eq_one (4119 : ZMod 12713)
      decide
    · apply IsUnit.of_mul_eq_one (11856 : ZMod 12713)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_12721 : Nat.Prime 12721 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 12721 12720 1 13 [2, 2, 2, 2, 3, 5, 53]
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
    · apply IsUnit.of_mul_eq_one (6360 : ZMod 12721)
      decide
    · apply IsUnit.of_mul_eq_one (11077 : ZMod 12721)
      decide
    · apply IsUnit.of_mul_eq_one (409 : ZMod 12721)
      decide
    · apply IsUnit.of_mul_eq_one (6892 : ZMod 12721)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_12739 : Nat.Prime 12739 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 12739 12738 1 2 [2, 3, 11, 193]
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
    · apply IsUnit.of_mul_eq_one (6369 : ZMod 12739)
      decide
    · apply IsUnit.of_mul_eq_one (2384 : ZMod 12739)
      decide
    · apply IsUnit.of_mul_eq_one (5470 : ZMod 12739)
      decide
    · apply IsUnit.of_mul_eq_one (4199 : ZMod 12739)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_12743 : Nat.Prime 12743 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 12743 12742 1 5 [2, 23, 277]
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
    · apply IsUnit.of_mul_eq_one (6371 : ZMod 12743)
      decide
    · apply IsUnit.of_mul_eq_one (11691 : ZMod 12743)
      decide
    · apply IsUnit.of_mul_eq_one (8739 : ZMod 12743)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_12757 : Nat.Prime 12757 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 12757 12756 1 2 [2, 2, 3, 1063]
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
    · apply IsUnit.of_mul_eq_one (6378 : ZMod 12757)
      decide
    · apply IsUnit.of_mul_eq_one (9293 : ZMod 12757)
      decide
    · apply IsUnit.of_mul_eq_one (8838 : ZMod 12757)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_12763 : Nat.Prime 12763 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 12763 12762 1 2 [2, 3, 3, 709]
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
    · apply IsUnit.of_mul_eq_one (6381 : ZMod 12763)
      decide
    · apply IsUnit.of_mul_eq_one (7497 : ZMod 12763)
      decide
    · apply IsUnit.of_mul_eq_one (3792 : ZMod 12763)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_12781 : Nat.Prime 12781 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 12781 12780 1 2 [2, 2, 3, 3, 5, 71]
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
    · apply IsUnit.of_mul_eq_one (6390 : ZMod 12781)
      decide
    · apply IsUnit.of_mul_eq_one (1074 : ZMod 12781)
      decide
    · apply IsUnit.of_mul_eq_one (8861 : ZMod 12781)
      decide
    · apply IsUnit.of_mul_eq_one (10809 : ZMod 12781)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_12791 : Nat.Prime 12791 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 12791 12790 1 7 [2, 5, 1279]
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
    · apply IsUnit.of_mul_eq_one (6395 : ZMod 12791)
      decide
    · apply IsUnit.of_mul_eq_one (131 : ZMod 12791)
      decide
    · apply IsUnit.of_mul_eq_one (7219 : ZMod 12791)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_12799 : Nat.Prime 12799 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 12799 12798 1 13 [2, 3, 3, 3, 3, 79]
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
    · apply IsUnit.of_mul_eq_one (6399 : ZMod 12799)
      decide
    · apply IsUnit.of_mul_eq_one (7726 : ZMod 12799)
      decide
    · apply IsUnit.of_mul_eq_one (4348 : ZMod 12799)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_12809 : Nat.Prime 12809 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 12809 12808 1 3 [2, 2, 2, 1601]
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
    · apply IsUnit.of_mul_eq_one (6404 : ZMod 12809)
      decide
    · apply IsUnit.of_mul_eq_one (7949 : ZMod 12809)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_12821 : Nat.Prime 12821 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 12821 12820 1 2 [2, 2, 5, 641]
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
    · apply IsUnit.of_mul_eq_one (6410 : ZMod 12821)
      decide
    · apply IsUnit.of_mul_eq_one (10098 : ZMod 12821)
      decide
    · apply IsUnit.of_mul_eq_one (2567 : ZMod 12821)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_12823 : Nat.Prime 12823 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 12823 12822 1 3 [2, 3, 2137]
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
    · apply IsUnit.of_mul_eq_one (6411 : ZMod 12823)
      decide
    · apply IsUnit.of_mul_eq_one (9012 : ZMod 12823)
      decide
    · apply IsUnit.of_mul_eq_one (1004 : ZMod 12823)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_12829 : Nat.Prime 12829 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 12829 12828 1 2 [2, 2, 3, 1069]
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
    · apply IsUnit.of_mul_eq_one (6414 : ZMod 12829)
      decide
    · apply IsUnit.of_mul_eq_one (7996 : ZMod 12829)
      decide
    · apply IsUnit.of_mul_eq_one (2995 : ZMod 12829)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_12841 : Nat.Prime 12841 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 12841 12840 1 21 [2, 2, 2, 3, 5, 107]
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
    · apply IsUnit.of_mul_eq_one (6420 : ZMod 12841)
      decide
    · apply IsUnit.of_mul_eq_one (1917 : ZMod 12841)
      decide
    · apply IsUnit.of_mul_eq_one (9998 : ZMod 12841)
      decide
    · apply IsUnit.of_mul_eq_one (10763 : ZMod 12841)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_12853 : Nat.Prime 12853 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 12853 12852 1 5 [2, 2, 3, 3, 3, 7, 17]
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
    · apply IsUnit.of_mul_eq_one (6426 : ZMod 12853)
      decide
    · apply IsUnit.of_mul_eq_one (6544 : ZMod 12853)
      decide
    · apply IsUnit.of_mul_eq_one (5835 : ZMod 12853)
      decide
    · apply IsUnit.of_mul_eq_one (1482 : ZMod 12853)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_12889 : Nat.Prime 12889 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 12889 12888 1 13 [2, 2, 2, 3, 3, 179]
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
    · apply IsUnit.of_mul_eq_one (6444 : ZMod 12889)
      decide
    · apply IsUnit.of_mul_eq_one (1419 : ZMod 12889)
      decide
    · apply IsUnit.of_mul_eq_one (11563 : ZMod 12889)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_12893 : Nat.Prime 12893 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 12893 12892 1 3 [2, 2, 11, 293]
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
    · apply IsUnit.of_mul_eq_one (6446 : ZMod 12893)
      decide
    · apply IsUnit.of_mul_eq_one (7505 : ZMod 12893)
      decide
    · apply IsUnit.of_mul_eq_one (12725 : ZMod 12893)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_12899 : Nat.Prime 12899 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 12899 12898 1 2 [2, 6449]
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
    · apply IsUnit.of_mul_eq_one (6449 : ZMod 12899)
      decide
    · apply IsUnit.of_mul_eq_one (4300 : ZMod 12899)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_12907 : Nat.Prime 12907 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 12907 12906 1 2 [2, 3, 3, 3, 239]
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
    · apply IsUnit.of_mul_eq_one (6453 : ZMod 12907)
      decide
    · apply IsUnit.of_mul_eq_one (11927 : ZMod 12907)
      decide
    · apply IsUnit.of_mul_eq_one (10694 : ZMod 12907)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_12911 : Nat.Prime 12911 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 12911 12910 1 23 [2, 5, 1291]
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
    · apply IsUnit.of_mul_eq_one (6455 : ZMod 12911)
      decide
    · apply IsUnit.of_mul_eq_one (3482 : ZMod 12911)
      decide
    · apply IsUnit.of_mul_eq_one (12198 : ZMod 12911)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_12917 : Nat.Prime 12917 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 12917 12916 1 2 [2, 2, 3229]
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
    · apply IsUnit.of_mul_eq_one (6458 : ZMod 12917)
      decide
    · apply IsUnit.of_mul_eq_one (6028 : ZMod 12917)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_12919 : Nat.Prime 12919 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 12919 12918 1 6 [2, 3, 2153]
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
    · apply IsUnit.of_mul_eq_one (6459 : ZMod 12919)
      decide
    · apply IsUnit.of_mul_eq_one (6772 : ZMod 12919)
      decide
    · apply IsUnit.of_mul_eq_one (705 : ZMod 12919)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_12923 : Nat.Prime 12923 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 12923 12922 1 2 [2, 7, 13, 71]
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
    · apply IsUnit.of_mul_eq_one (6461 : ZMod 12923)
      decide
    · apply IsUnit.of_mul_eq_one (2364 : ZMod 12923)
      decide
    · apply IsUnit.of_mul_eq_one (710 : ZMod 12923)
      decide
    · apply IsUnit.of_mul_eq_one (204 : ZMod 12923)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_12941 : Nat.Prime 12941 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 12941 12940 1 2 [2, 2, 5, 647]
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
    · apply IsUnit.of_mul_eq_one (6470 : ZMod 12941)
      decide
    · apply IsUnit.of_mul_eq_one (11933 : ZMod 12941)
      decide
    · apply IsUnit.of_mul_eq_one (4204 : ZMod 12941)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_12953 : Nat.Prime 12953 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 12953 12952 1 3 [2, 2, 2, 1619]
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
    · apply IsUnit.of_mul_eq_one (6476 : ZMod 12953)
      decide
    · apply IsUnit.of_mul_eq_one (10471 : ZMod 12953)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_12959 : Nat.Prime 12959 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 12959 12958 1 7 [2, 11, 19, 31]
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
    · apply IsUnit.of_mul_eq_one (6479 : ZMod 12959)
      decide
    · apply IsUnit.of_mul_eq_one (5493 : ZMod 12959)
      decide
    · apply IsUnit.of_mul_eq_one (1943 : ZMod 12959)
      decide
    · apply IsUnit.of_mul_eq_one (5925 : ZMod 12959)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_12967 : Nat.Prime 12967 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 12967 12966 1 3 [2, 3, 2161]
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
    · apply IsUnit.of_mul_eq_one (6483 : ZMod 12967)
      decide
    · apply IsUnit.of_mul_eq_one (10550 : ZMod 12967)
      decide
    · apply IsUnit.of_mul_eq_one (8140 : ZMod 12967)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_12973 : Nat.Prime 12973 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 12973 12972 1 14 [2, 2, 3, 23, 47]
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
    · apply IsUnit.of_mul_eq_one (6486 : ZMod 12973)
      decide
    · apply IsUnit.of_mul_eq_one (6286 : ZMod 12973)
      decide
    · apply IsUnit.of_mul_eq_one (6563 : ZMod 12973)
      decide
    · apply IsUnit.of_mul_eq_one (8449 : ZMod 12973)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_12979 : Nat.Prime 12979 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 12979 12978 1 2 [2, 3, 3, 7, 103]
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
    · apply IsUnit.of_mul_eq_one (6489 : ZMod 12979)
      decide
    · apply IsUnit.of_mul_eq_one (1280 : ZMod 12979)
      decide
    · apply IsUnit.of_mul_eq_one (7548 : ZMod 12979)
      decide
    · apply IsUnit.of_mul_eq_one (12058 : ZMod 12979)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_12983 : Nat.Prime 12983 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 12983 12982 1 5 [2, 6491]
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
    · apply IsUnit.of_mul_eq_one (6491 : ZMod 12983)
      decide
    · apply IsUnit.of_mul_eq_one (541 : ZMod 12983)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_13001 : Nat.Prime 13001 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 13001 13000 1 3 [2, 2, 2, 5, 5, 5, 13]
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
    · apply IsUnit.of_mul_eq_one (6500 : ZMod 13001)
      decide
    · apply IsUnit.of_mul_eq_one (10677 : ZMod 13001)
      decide
    · apply IsUnit.of_mul_eq_one (9781 : ZMod 13001)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_13003 : Nat.Prime 13003 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 13003 13002 1 5 [2, 3, 11, 197]
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
    · apply IsUnit.of_mul_eq_one (6501 : ZMod 13003)
      decide
    · apply IsUnit.of_mul_eq_one (562 : ZMod 13003)
      decide
    · apply IsUnit.of_mul_eq_one (1109 : ZMod 13003)
      decide
    · apply IsUnit.of_mul_eq_one (4618 : ZMod 13003)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_13007 : Nat.Prime 13007 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 13007 13006 1 5 [2, 7, 929]
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
    · apply IsUnit.of_mul_eq_one (6503 : ZMod 13007)
      decide
    · apply IsUnit.of_mul_eq_one (1412 : ZMod 13007)
      decide
    · apply IsUnit.of_mul_eq_one (9066 : ZMod 13007)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_13009 : Nat.Prime 13009 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 13009 13008 1 7 [2, 2, 2, 2, 3, 271]
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
    · apply IsUnit.of_mul_eq_one (6504 : ZMod 13009)
      decide
    · apply IsUnit.of_mul_eq_one (5673 : ZMod 13009)
      decide
    · apply IsUnit.of_mul_eq_one (7014 : ZMod 13009)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_13033 : Nat.Prime 13033 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 13033 13032 1 5 [2, 2, 2, 3, 3, 181]
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
    · apply IsUnit.of_mul_eq_one (6516 : ZMod 13033)
      decide
    · apply IsUnit.of_mul_eq_one (9429 : ZMod 13033)
      decide
    · apply IsUnit.of_mul_eq_one (4308 : ZMod 13033)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_13037 : Nat.Prime 13037 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 13037 13036 1 2 [2, 2, 3259]
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
    · apply IsUnit.of_mul_eq_one (6518 : ZMod 13037)
      decide
    · apply IsUnit.of_mul_eq_one (6084 : ZMod 13037)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_13043 : Nat.Prime 13043 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 13043 13042 1 2 [2, 6521]
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
    · apply IsUnit.of_mul_eq_one (6521 : ZMod 13043)
      decide
    · apply IsUnit.of_mul_eq_one (4348 : ZMod 13043)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_13049 : Nat.Prime 13049 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 13049 13048 1 3 [2, 2, 2, 7, 233]
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
    · apply IsUnit.of_mul_eq_one (6524 : ZMod 13049)
      decide
    · apply IsUnit.of_mul_eq_one (1367 : ZMod 13049)
      decide
    · apply IsUnit.of_mul_eq_one (5250 : ZMod 13049)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_13063 : Nat.Prime 13063 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 13063 13062 1 5 [2, 3, 7, 311]
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
    · apply IsUnit.of_mul_eq_one (6531 : ZMod 13063)
      decide
    · apply IsUnit.of_mul_eq_one (4803 : ZMod 13063)
      decide
    · apply IsUnit.of_mul_eq_one (6029 : ZMod 13063)
      decide
    · apply IsUnit.of_mul_eq_one (11075 : ZMod 13063)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_13093 : Nat.Prime 13093 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 13093 13092 1 6 [2, 2, 3, 1091]
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
    · apply IsUnit.of_mul_eq_one (6546 : ZMod 13093)
      decide
    · apply IsUnit.of_mul_eq_one (9158 : ZMod 13093)
      decide
    · apply IsUnit.of_mul_eq_one (11376 : ZMod 13093)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_13099 : Nat.Prime 13099 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 13099 13098 1 3 [2, 3, 37, 59]
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
    · apply IsUnit.of_mul_eq_one (6549 : ZMod 13099)
      decide
    · apply IsUnit.of_mul_eq_one (10271 : ZMod 13099)
      decide
    · apply IsUnit.of_mul_eq_one (3049 : ZMod 13099)
      decide
    · apply IsUnit.of_mul_eq_one (10509 : ZMod 13099)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_13103 : Nat.Prime 13103 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 13103 13102 1 5 [2, 6551]
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
    · apply IsUnit.of_mul_eq_one (6551 : ZMod 13103)
      decide
    · apply IsUnit.of_mul_eq_one (546 : ZMod 13103)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_13109 : Nat.Prime 13109 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 13109 13108 1 2 [2, 2, 29, 113]
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
    · apply IsUnit.of_mul_eq_one (6554 : ZMod 13109)
      decide
    · apply IsUnit.of_mul_eq_one (12698 : ZMod 13109)
      decide
    · apply IsUnit.of_mul_eq_one (4325 : ZMod 13109)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_13121 : Nat.Prime 13121 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 13121 13120 1 7 [2, 2, 2, 2, 2, 2, 5, 41]
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
    · apply IsUnit.of_mul_eq_one (6560 : ZMod 13121)
      decide
    · apply IsUnit.of_mul_eq_one (7246 : ZMod 13121)
      decide
    · apply IsUnit.of_mul_eq_one (9941 : ZMod 13121)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_13127 : Nat.Prime 13127 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 13127 13126 1 5 [2, 6563]
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
    · apply IsUnit.of_mul_eq_one (6563 : ZMod 13127)
      decide
    · apply IsUnit.of_mul_eq_one (547 : ZMod 13127)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_13147 : Nat.Prime 13147 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 13147 13146 1 2 [2, 3, 7, 313]
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
    · apply IsUnit.of_mul_eq_one (6573 : ZMod 13147)
      decide
    · apply IsUnit.of_mul_eq_one (12515 : ZMod 13147)
      decide
    · apply IsUnit.of_mul_eq_one (8180 : ZMod 13147)
      decide
    · apply IsUnit.of_mul_eq_one (9613 : ZMod 13147)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_13151 : Nat.Prime 13151 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 13151 13150 1 13 [2, 5, 5, 263]
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
    · apply IsUnit.of_mul_eq_one (6575 : ZMod 13151)
      decide
    · apply IsUnit.of_mul_eq_one (251 : ZMod 13151)
      decide
    · apply IsUnit.of_mul_eq_one (9639 : ZMod 13151)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_13159 : Nat.Prime 13159 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 13159 13158 1 3 [2, 3, 3, 17, 43]
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
    · apply IsUnit.of_mul_eq_one (6579 : ZMod 13159)
      decide
    · apply IsUnit.of_mul_eq_one (8671 : ZMod 13159)
      decide
    · apply IsUnit.of_mul_eq_one (6336 : ZMod 13159)
      decide
    · apply IsUnit.of_mul_eq_one (7451 : ZMod 13159)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_13163 : Nat.Prime 13163 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 13163 13162 1 2 [2, 6581]
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
    · apply IsUnit.of_mul_eq_one (6581 : ZMod 13163)
      decide
    · apply IsUnit.of_mul_eq_one (4388 : ZMod 13163)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_13171 : Nat.Prime 13171 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 13171 13170 1 11 [2, 3, 5, 439]
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
    · apply IsUnit.of_mul_eq_one (6585 : ZMod 13171)
      decide
    · apply IsUnit.of_mul_eq_one (11215 : ZMod 13171)
      decide
    · apply IsUnit.of_mul_eq_one (302 : ZMod 13171)
      decide
    · apply IsUnit.of_mul_eq_one (8691 : ZMod 13171)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_13177 : Nat.Prime 13177 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 13177 13176 1 5 [2, 2, 2, 3, 3, 3, 61]
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
    · apply IsUnit.of_mul_eq_one (6588 : ZMod 13177)
      decide
    · apply IsUnit.of_mul_eq_one (9790 : ZMod 13177)
      decide
    · apply IsUnit.of_mul_eq_one (4466 : ZMod 13177)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_13183 : Nat.Prime 13183 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 13183 13182 1 3 [2, 3, 13, 13, 13]
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
    · apply IsUnit.of_mul_eq_one (6591 : ZMod 13183)
      decide
    · apply IsUnit.of_mul_eq_one (4973 : ZMod 13183)
      decide
    · apply IsUnit.of_mul_eq_one (2299 : ZMod 13183)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_13187 : Nat.Prime 13187 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 13187 13186 1 2 [2, 19, 347]
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
    · apply IsUnit.of_mul_eq_one (6593 : ZMod 13187)
      decide
    · apply IsUnit.of_mul_eq_one (6384 : ZMod 13187)
      decide
    · apply IsUnit.of_mul_eq_one (7007 : ZMod 13187)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_13217 : Nat.Prime 13217 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 13217 13216 1 3 [2, 2, 2, 2, 2, 7, 59]
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
    · apply IsUnit.of_mul_eq_one (6608 : ZMod 13217)
      decide
    · apply IsUnit.of_mul_eq_one (3824 : ZMod 13217)
      decide
    · apply IsUnit.of_mul_eq_one (6257 : ZMod 13217)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_13219 : Nat.Prime 13219 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 13219 13218 1 3 [2, 3, 2203]
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
    · apply IsUnit.of_mul_eq_one (6609 : ZMod 13219)
      decide
    · apply IsUnit.of_mul_eq_one (6904 : ZMod 13219)
      decide
    · apply IsUnit.of_mul_eq_one (12874 : ZMod 13219)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_13229 : Nat.Prime 13229 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 13229 13228 1 2 [2, 2, 3307]
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
    · apply IsUnit.of_mul_eq_one (6614 : ZMod 13229)
      decide
    · apply IsUnit.of_mul_eq_one (882 : ZMod 13229)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_13241 : Nat.Prime 13241 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 13241 13240 1 3 [2, 2, 2, 5, 331]
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
    · apply IsUnit.of_mul_eq_one (6620 : ZMod 13241)
      decide
    · apply IsUnit.of_mul_eq_one (779 : ZMod 13241)
      decide
    · apply IsUnit.of_mul_eq_one (4678 : ZMod 13241)
      decide
  · norm_num
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_12097_12712_part05 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_12708 (p := 12391) (q := 12401) (by exact lowPrime_12401) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12708 (p := 12401) (q := 12409) (by exact lowPrime_12409) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12708 (p := 12409) (q := 12413) (by exact lowPrime_12413) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12708 (p := 12413) (q := 12421) (by exact lowPrime_12421) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12708 (p := 12421) (q := 12433) (by exact lowPrime_12433) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12708 (p := 12433) (q := 12437) (by exact lowPrime_12437) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12708 (p := 12437) (q := 12451) (by exact lowPrime_12451) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12708 (p := 12451) (q := 12457) (by exact lowPrime_12457) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_12097_12712_part05_chain :
    DusartPrimeRowsChain 12391 12456 dusartPrimeRows_12097_12712_part05 := by
  apply DusartPrimeRowsChain.cons
  · norm_num [dusartPrimeRow_of_explicit_12708]
  · norm_num [dusartPrimeRow_of_explicit_12708]
  · apply DusartPrimeRowsChain.cons
    · norm_num [dusartPrimeRow_of_explicit_12708]
    · norm_num [dusartPrimeRow_of_explicit_12708]
    · apply DusartPrimeRowsChain.cons
      · norm_num [dusartPrimeRow_of_explicit_12708]
      · norm_num [dusartPrimeRow_of_explicit_12708]
      · apply DusartPrimeRowsChain.cons
        · norm_num [dusartPrimeRow_of_explicit_12708]
        · norm_num [dusartPrimeRow_of_explicit_12708]
        · apply DusartPrimeRowsChain.cons
          · norm_num [dusartPrimeRow_of_explicit_12708]
          · norm_num [dusartPrimeRow_of_explicit_12708]
          · apply DusartPrimeRowsChain.cons
            · norm_num [dusartPrimeRow_of_explicit_12708]
            · norm_num [dusartPrimeRow_of_explicit_12708]
            · apply DusartPrimeRowsChain.cons
              · norm_num [dusartPrimeRow_of_explicit_12708]
              · norm_num [dusartPrimeRow_of_explicit_12708]
              · apply DusartPrimeRowsChain.cons
                · norm_num [dusartPrimeRow_of_explicit_12708]
                · norm_num [dusartPrimeRow_of_explicit_12708]
                · apply DusartPrimeRowsChain.empty
                  norm_num [dusartPrimeRow_of_explicit_12708, dusartPrimeRow_of_explicit_right]

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_12097_12712_part06 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_12708 (p := 12457) (q := 12473) (by exact lowPrime_12473) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12708 (p := 12473) (q := 12479) (by exact lowPrime_12479) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12708 (p := 12479) (q := 12487) (by exact lowPrime_12487) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12708 (p := 12487) (q := 12491) (by exact lowPrime_12491) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12708 (p := 12491) (q := 12497) (by exact lowPrime_12497) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12708 (p := 12497) (q := 12503) (by exact lowPrime_12503) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12708 (p := 12503) (q := 12511) (by exact lowPrime_12511) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12708 (p := 12511) (q := 12517) (by exact lowPrime_12517) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_12097_12712_part06_chain :
    DusartPrimeRowsChain 12457 12516 dusartPrimeRows_12097_12712_part06 := by
  apply DusartPrimeRowsChain.cons
  · norm_num [dusartPrimeRow_of_explicit_12708]
  · norm_num [dusartPrimeRow_of_explicit_12708]
  · apply DusartPrimeRowsChain.cons
    · norm_num [dusartPrimeRow_of_explicit_12708]
    · norm_num [dusartPrimeRow_of_explicit_12708]
    · apply DusartPrimeRowsChain.cons
      · norm_num [dusartPrimeRow_of_explicit_12708]
      · norm_num [dusartPrimeRow_of_explicit_12708]
      · apply DusartPrimeRowsChain.cons
        · norm_num [dusartPrimeRow_of_explicit_12708]
        · norm_num [dusartPrimeRow_of_explicit_12708]
        · apply DusartPrimeRowsChain.cons
          · norm_num [dusartPrimeRow_of_explicit_12708]
          · norm_num [dusartPrimeRow_of_explicit_12708]
          · apply DusartPrimeRowsChain.cons
            · norm_num [dusartPrimeRow_of_explicit_12708]
            · norm_num [dusartPrimeRow_of_explicit_12708]
            · apply DusartPrimeRowsChain.cons
              · norm_num [dusartPrimeRow_of_explicit_12708]
              · norm_num [dusartPrimeRow_of_explicit_12708]
              · apply DusartPrimeRowsChain.cons
                · norm_num [dusartPrimeRow_of_explicit_12708]
                · norm_num [dusartPrimeRow_of_explicit_12708]
                · apply DusartPrimeRowsChain.empty
                  norm_num [dusartPrimeRow_of_explicit_12708, dusartPrimeRow_of_explicit_right]

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_12097_12712_part07 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_12708 (p := 12517) (q := 12527) (by exact lowPrime_12527) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12708 (p := 12527) (q := 12539) (by exact lowPrime_12539) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12708 (p := 12539) (q := 12541) (by exact lowPrime_12541) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12708 (p := 12541) (q := 12547) (by exact lowPrime_12547) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12708 (p := 12547) (q := 12553) (by exact lowPrime_12553) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12708 (p := 12553) (q := 12569) (by exact lowPrime_12569) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12708 (p := 12569) (q := 12577) (by exact lowPrime_12577) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12708 (p := 12577) (q := 12583) (by exact lowPrime_12583) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_12097_12712_part07_chain :
    DusartPrimeRowsChain 12517 12582 dusartPrimeRows_12097_12712_part07 := by
  apply DusartPrimeRowsChain.cons
  · norm_num [dusartPrimeRow_of_explicit_12708]
  · norm_num [dusartPrimeRow_of_explicit_12708]
  · apply DusartPrimeRowsChain.cons
    · norm_num [dusartPrimeRow_of_explicit_12708]
    · norm_num [dusartPrimeRow_of_explicit_12708]
    · apply DusartPrimeRowsChain.cons
      · norm_num [dusartPrimeRow_of_explicit_12708]
      · norm_num [dusartPrimeRow_of_explicit_12708]
      · apply DusartPrimeRowsChain.cons
        · norm_num [dusartPrimeRow_of_explicit_12708]
        · norm_num [dusartPrimeRow_of_explicit_12708]
        · apply DusartPrimeRowsChain.cons
          · norm_num [dusartPrimeRow_of_explicit_12708]
          · norm_num [dusartPrimeRow_of_explicit_12708]
          · apply DusartPrimeRowsChain.cons
            · norm_num [dusartPrimeRow_of_explicit_12708]
            · norm_num [dusartPrimeRow_of_explicit_12708]
            · apply DusartPrimeRowsChain.cons
              · norm_num [dusartPrimeRow_of_explicit_12708]
              · norm_num [dusartPrimeRow_of_explicit_12708]
              · apply DusartPrimeRowsChain.cons
                · norm_num [dusartPrimeRow_of_explicit_12708]
                · norm_num [dusartPrimeRow_of_explicit_12708]
                · apply DusartPrimeRowsChain.empty
                  norm_num [dusartPrimeRow_of_explicit_12708, dusartPrimeRow_of_explicit_right]

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_12097_12712_part08 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_12708 (p := 12583) (q := 12589) (by exact lowPrime_12589) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12708 (p := 12589) (q := 12601) (by exact lowPrime_12601) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12708 (p := 12601) (q := 12611) (by exact lowPrime_12611) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12708 (p := 12611) (q := 12613) (by exact lowPrime_12613) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12708 (p := 12613) (q := 12619) (by exact lowPrime_12619) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12708 (p := 12619) (q := 12637) (by exact lowPrime_12637) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12708 (p := 12637) (q := 12641) (by exact lowPrime_12641) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12708 (p := 12641) (q := 12647) (by exact lowPrime_12647) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_12097_12712_part08_chain :
    DusartPrimeRowsChain 12583 12646 dusartPrimeRows_12097_12712_part08 := by
  apply DusartPrimeRowsChain.cons
  · norm_num [dusartPrimeRow_of_explicit_12708]
  · norm_num [dusartPrimeRow_of_explicit_12708]
  · apply DusartPrimeRowsChain.cons
    · norm_num [dusartPrimeRow_of_explicit_12708]
    · norm_num [dusartPrimeRow_of_explicit_12708]
    · apply DusartPrimeRowsChain.cons
      · norm_num [dusartPrimeRow_of_explicit_12708]
      · norm_num [dusartPrimeRow_of_explicit_12708]
      · apply DusartPrimeRowsChain.cons
        · norm_num [dusartPrimeRow_of_explicit_12708]
        · norm_num [dusartPrimeRow_of_explicit_12708]
        · apply DusartPrimeRowsChain.cons
          · norm_num [dusartPrimeRow_of_explicit_12708]
          · norm_num [dusartPrimeRow_of_explicit_12708]
          · apply DusartPrimeRowsChain.cons
            · norm_num [dusartPrimeRow_of_explicit_12708]
            · norm_num [dusartPrimeRow_of_explicit_12708]
            · apply DusartPrimeRowsChain.cons
              · norm_num [dusartPrimeRow_of_explicit_12708]
              · norm_num [dusartPrimeRow_of_explicit_12708]
              · apply DusartPrimeRowsChain.cons
                · norm_num [dusartPrimeRow_of_explicit_12708]
                · norm_num [dusartPrimeRow_of_explicit_12708]
                · apply DusartPrimeRowsChain.empty
                  norm_num [dusartPrimeRow_of_explicit_12708, dusartPrimeRow_of_explicit_right]

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_12097_12712_part09 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_12708 (p := 12647) (q := 12653) (by exact lowPrime_12653) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12708 (p := 12653) (q := 12659) (by exact lowPrime_12659) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12708 (p := 12659) (q := 12671) (by exact lowPrime_12671) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12708 (p := 12671) (q := 12689) (by exact lowPrime_12689) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12708 (p := 12689) (q := 12697) (by exact lowPrime_12697) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12708 (p := 12697) (q := 12703) (by exact lowPrime_12703) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12708 (p := 12703) (q := 12713) (by exact lowPrime_12713) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_12097_12712_part09_chain :
    DusartPrimeRowsChain 12647 12712 dusartPrimeRows_12097_12712_part09 := by
  apply DusartPrimeRowsChain.cons
  · norm_num [dusartPrimeRow_of_explicit_12708]
  · norm_num [dusartPrimeRow_of_explicit_12708]
  · apply DusartPrimeRowsChain.cons
    · norm_num [dusartPrimeRow_of_explicit_12708]
    · norm_num [dusartPrimeRow_of_explicit_12708]
    · apply DusartPrimeRowsChain.cons
      · norm_num [dusartPrimeRow_of_explicit_12708]
      · norm_num [dusartPrimeRow_of_explicit_12708]
      · apply DusartPrimeRowsChain.cons
        · norm_num [dusartPrimeRow_of_explicit_12708]
        · norm_num [dusartPrimeRow_of_explicit_12708]
        · apply DusartPrimeRowsChain.cons
          · norm_num [dusartPrimeRow_of_explicit_12708]
          · norm_num [dusartPrimeRow_of_explicit_12708]
          · apply DusartPrimeRowsChain.cons
            · norm_num [dusartPrimeRow_of_explicit_12708]
            · norm_num [dusartPrimeRow_of_explicit_12708]
            · apply DusartPrimeRowsChain.cons
              · norm_num [dusartPrimeRow_of_explicit_12708]
              · norm_num [dusartPrimeRow_of_explicit_12708]
              · apply DusartPrimeRowsChain.empty
                norm_num [dusartPrimeRow_of_explicit_12708, dusartPrimeRow_of_explicit_right]

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_12713_13366_part01 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_13359 (p := 12713) (q := 12721) (by exact lowPrime_12721) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_13359 (p := 12721) (q := 12739) (by exact lowPrime_12739) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_13359 (p := 12739) (q := 12743) (by exact lowPrime_12743) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_13359 (p := 12743) (q := 12757) (by exact lowPrime_12757) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_13359 (p := 12757) (q := 12763) (by exact lowPrime_12763) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_13359 (p := 12763) (q := 12781) (by exact lowPrime_12781) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_13359 (p := 12781) (q := 12791) (by exact lowPrime_12791) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_13359 (p := 12791) (q := 12799) (by exact lowPrime_12799) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_12713_13366_part01_chain :
    DusartPrimeRowsChain 12713 12798 dusartPrimeRows_12713_13366_part01 := by
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
def dusartPrimeRows_12713_13366_part02 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_13359 (p := 12799) (q := 12809) (by exact lowPrime_12809) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_13359 (p := 12809) (q := 12821) (by exact lowPrime_12821) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_13359 (p := 12821) (q := 12823) (by exact lowPrime_12823) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_13359 (p := 12823) (q := 12829) (by exact lowPrime_12829) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_13359 (p := 12829) (q := 12841) (by exact lowPrime_12841) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_13359 (p := 12841) (q := 12853) (by exact lowPrime_12853) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_13359 (p := 12853) (q := 12889) (by exact lowPrime_12889) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_13359 (p := 12889) (q := 12893) (by exact lowPrime_12893) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_12713_13366_part02_chain :
    DusartPrimeRowsChain 12799 12892 dusartPrimeRows_12713_13366_part02 := by
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
def dusartPrimeRows_12713_13366_part03 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_13359 (p := 12893) (q := 12899) (by exact lowPrime_12899) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_13359 (p := 12899) (q := 12907) (by exact lowPrime_12907) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_13359 (p := 12907) (q := 12911) (by exact lowPrime_12911) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_13359 (p := 12911) (q := 12917) (by exact lowPrime_12917) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_13359 (p := 12917) (q := 12919) (by exact lowPrime_12919) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_13359 (p := 12919) (q := 12923) (by exact lowPrime_12923) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_13359 (p := 12923) (q := 12941) (by exact lowPrime_12941) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_13359 (p := 12941) (q := 12953) (by exact lowPrime_12953) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_12713_13366_part03_chain :
    DusartPrimeRowsChain 12893 12952 dusartPrimeRows_12713_13366_part03 := by
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
def dusartPrimeRows_12713_13366_part04 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_13359 (p := 12953) (q := 12959) (by exact lowPrime_12959) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_13359 (p := 12959) (q := 12967) (by exact lowPrime_12967) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_13359 (p := 12967) (q := 12973) (by exact lowPrime_12973) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_13359 (p := 12973) (q := 12979) (by exact lowPrime_12979) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_13359 (p := 12979) (q := 12983) (by exact lowPrime_12983) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_13359 (p := 12983) (q := 13001) (by exact lowPrime_13001) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_13359 (p := 13001) (q := 13003) (by exact lowPrime_13003) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_13359 (p := 13003) (q := 13007) (by exact lowPrime_13007) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_12713_13366_part04_chain :
    DusartPrimeRowsChain 12953 13006 dusartPrimeRows_12713_13366_part04 := by
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
def dusartPrimeRows_12713_13366_part05 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_13359 (p := 13007) (q := 13009) (by exact lowPrime_13009) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_13359 (p := 13009) (q := 13033) (by exact lowPrime_13033) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_13359 (p := 13033) (q := 13037) (by exact lowPrime_13037) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_13359 (p := 13037) (q := 13043) (by exact lowPrime_13043) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_13359 (p := 13043) (q := 13049) (by exact lowPrime_13049) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_13359 (p := 13049) (q := 13063) (by exact lowPrime_13063) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_13359 (p := 13063) (q := 13093) (by exact lowPrime_13093) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_13359 (p := 13093) (q := 13099) (by exact lowPrime_13099) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_12713_13366_part05_chain :
    DusartPrimeRowsChain 13007 13098 dusartPrimeRows_12713_13366_part05 := by
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
def dusartPrimeRows_12713_13366_part06 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_13359 (p := 13099) (q := 13103) (by exact lowPrime_13103) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_13359 (p := 13103) (q := 13109) (by exact lowPrime_13109) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_13359 (p := 13109) (q := 13121) (by exact lowPrime_13121) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_13359 (p := 13121) (q := 13127) (by exact lowPrime_13127) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_13359 (p := 13127) (q := 13147) (by exact lowPrime_13147) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_13359 (p := 13147) (q := 13151) (by exact lowPrime_13151) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_13359 (p := 13151) (q := 13159) (by exact lowPrime_13159) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_13359 (p := 13159) (q := 13163) (by exact lowPrime_13163) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_12713_13366_part06_chain :
    DusartPrimeRowsChain 13099 13162 dusartPrimeRows_12713_13366_part06 := by
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
def dusartPrimeRows_12713_13366_part07 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_13359 (p := 13163) (q := 13171) (by exact lowPrime_13171) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_13359 (p := 13171) (q := 13177) (by exact lowPrime_13177) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_13359 (p := 13177) (q := 13183) (by exact lowPrime_13183) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_13359 (p := 13183) (q := 13187) (by exact lowPrime_13187) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_13359 (p := 13187) (q := 13217) (by exact lowPrime_13217) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_13359 (p := 13217) (q := 13219) (by exact lowPrime_13219) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_13359 (p := 13219) (q := 13229) (by exact lowPrime_13229) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_13359 (p := 13229) (q := 13241) (by exact lowPrime_13241) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_12713_13366_part07_chain :
    DusartPrimeRowsChain 13163 13240 dusartPrimeRows_12713_13366_part07 := by
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
