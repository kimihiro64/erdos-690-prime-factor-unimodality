import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowBase

set_option autoImplicit false
set_option maxRecDepth 1000000

/-! # Lower finite Dusart prefix chunk 23 -/

namespace PrimeFactorUnimodality

noncomputable section
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_17167 : Nat.Prime 17167 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 17167 17166 1 3 [2, 3, 2861]
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
    · apply IsUnit.of_mul_eq_one (8583 : ZMod 17167)
      decide
    · apply IsUnit.of_mul_eq_one (1988 : ZMod 17167)
      decide
    · apply IsUnit.of_mul_eq_one (9456 : ZMod 17167)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_17183 : Nat.Prime 17183 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 17183 17182 1 5 [2, 11, 11, 71]
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
    · apply IsUnit.of_mul_eq_one (8591 : ZMod 17183)
      decide
    · apply IsUnit.of_mul_eq_one (8757 : ZMod 17183)
      decide
    · apply IsUnit.of_mul_eq_one (6133 : ZMod 17183)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_17189 : Nat.Prime 17189 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 17189 17188 1 2 [2, 2, 4297]
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
    · apply IsUnit.of_mul_eq_one (8594 : ZMod 17189)
      decide
    · apply IsUnit.of_mul_eq_one (1146 : ZMod 17189)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_17191 : Nat.Prime 17191 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 17191 17190 1 3 [2, 3, 3, 5, 191]
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
    · apply IsUnit.of_mul_eq_one (8595 : ZMod 17191)
      decide
    · apply IsUnit.of_mul_eq_one (10853 : ZMod 17191)
      decide
    · apply IsUnit.of_mul_eq_one (14803 : ZMod 17191)
      decide
    · apply IsUnit.of_mul_eq_one (10121 : ZMod 17191)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_17203 : Nat.Prime 17203 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 17203 17202 1 2 [2, 3, 47, 61]
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
    · apply IsUnit.of_mul_eq_one (8601 : ZMod 17203)
      decide
    · apply IsUnit.of_mul_eq_one (15740 : ZMod 17203)
      decide
    · apply IsUnit.of_mul_eq_one (191 : ZMod 17203)
      decide
    · apply IsUnit.of_mul_eq_one (6272 : ZMod 17203)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_17207 : Nat.Prime 17207 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 17207 17206 1 5 [2, 7, 1229]
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
    · apply IsUnit.of_mul_eq_one (8603 : ZMod 17207)
      decide
    · apply IsUnit.of_mul_eq_one (4719 : ZMod 17207)
      decide
    · apply IsUnit.of_mul_eq_one (5531 : ZMod 17207)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_17209 : Nat.Prime 17209 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 17209 17208 1 14 [2, 2, 2, 3, 3, 239]
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
    · apply IsUnit.of_mul_eq_one (8604 : ZMod 17209)
      decide
    · apply IsUnit.of_mul_eq_one (16486 : ZMod 17209)
      decide
    · apply IsUnit.of_mul_eq_one (6719 : ZMod 17209)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_17231 : Nat.Prime 17231 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 17231 17230 1 13 [2, 5, 1723]
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
    · apply IsUnit.of_mul_eq_one (8615 : ZMod 17231)
      decide
    · apply IsUnit.of_mul_eq_one (4035 : ZMod 17231)
      decide
    · apply IsUnit.of_mul_eq_one (16704 : ZMod 17231)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_17239 : Nat.Prime 17239 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 17239 17238 1 6 [2, 3, 13, 13, 17]
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
    · apply IsUnit.of_mul_eq_one (8619 : ZMod 17239)
      decide
    · apply IsUnit.of_mul_eq_one (12180 : ZMod 17239)
      decide
    · apply IsUnit.of_mul_eq_one (977 : ZMod 17239)
      decide
    · apply IsUnit.of_mul_eq_one (6885 : ZMod 17239)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_17257 : Nat.Prime 17257 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 17257 17256 1 5 [2, 2, 2, 3, 719]
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
    · apply IsUnit.of_mul_eq_one (8628 : ZMod 17257)
      decide
    · apply IsUnit.of_mul_eq_one (11047 : ZMod 17257)
      decide
    · apply IsUnit.of_mul_eq_one (3177 : ZMod 17257)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_17291 : Nat.Prime 17291 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 17291 17290 1 6 [2, 5, 7, 13, 19]
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
    · apply IsUnit.of_mul_eq_one (8645 : ZMod 17291)
      decide
    · apply IsUnit.of_mul_eq_one (13376 : ZMod 17291)
      decide
    · apply IsUnit.of_mul_eq_one (8543 : ZMod 17291)
      decide
    · apply IsUnit.of_mul_eq_one (2709 : ZMod 17291)
      decide
    · apply IsUnit.of_mul_eq_one (1176 : ZMod 17291)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_17293 : Nat.Prime 17293 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 17293 17292 1 7 [2, 2, 3, 11, 131]
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
    · apply IsUnit.of_mul_eq_one (8646 : ZMod 17293)
      decide
    · apply IsUnit.of_mul_eq_one (11572 : ZMod 17293)
      decide
    · apply IsUnit.of_mul_eq_one (16257 : ZMod 17293)
      decide
    · apply IsUnit.of_mul_eq_one (10519 : ZMod 17293)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_17299 : Nat.Prime 17299 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 17299 17298 1 2 [2, 3, 3, 31, 31]
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
    · apply IsUnit.of_mul_eq_one (8649 : ZMod 17299)
      decide
    · apply IsUnit.of_mul_eq_one (1907 : ZMod 17299)
      decide
    · apply IsUnit.of_mul_eq_one (5345 : ZMod 17299)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_17317 : Nat.Prime 17317 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 17317 17316 1 2 [2, 2, 3, 3, 13, 37]
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
    · apply IsUnit.of_mul_eq_one (8658 : ZMod 17317)
      decide
    · apply IsUnit.of_mul_eq_one (15177 : ZMod 17317)
      decide
    · apply IsUnit.of_mul_eq_one (13628 : ZMod 17317)
      decide
    · apply IsUnit.of_mul_eq_one (10493 : ZMod 17317)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_17321 : Nat.Prime 17321 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 17321 17320 1 3 [2, 2, 2, 5, 433]
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
    · apply IsUnit.of_mul_eq_one (8660 : ZMod 17321)
      decide
    · apply IsUnit.of_mul_eq_one (13962 : ZMod 17321)
      decide
    · apply IsUnit.of_mul_eq_one (16914 : ZMod 17321)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_17327 : Nat.Prime 17327 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 17327 17326 1 5 [2, 8663]
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
    · apply IsUnit.of_mul_eq_one (8663 : ZMod 17327)
      decide
    · apply IsUnit.of_mul_eq_one (722 : ZMod 17327)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_17333 : Nat.Prime 17333 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 17333 17332 1 2 [2, 2, 7, 619]
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
    · apply IsUnit.of_mul_eq_one (8666 : ZMod 17333)
      decide
    · apply IsUnit.of_mul_eq_one (457 : ZMod 17333)
      decide
    · apply IsUnit.of_mul_eq_one (4188 : ZMod 17333)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_17341 : Nat.Prime 17341 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 17341 17340 1 6 [2, 2, 3, 5, 17, 17]
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
    · apply IsUnit.of_mul_eq_one (8670 : ZMod 17341)
      decide
    · apply IsUnit.of_mul_eq_one (14546 : ZMod 17341)
      decide
    · apply IsUnit.of_mul_eq_one (11695 : ZMod 17341)
      decide
    · apply IsUnit.of_mul_eq_one (7077 : ZMod 17341)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_17351 : Nat.Prime 17351 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 17351 17350 1 11 [2, 5, 5, 347]
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
    · apply IsUnit.of_mul_eq_one (8675 : ZMod 17351)
      decide
    · apply IsUnit.of_mul_eq_one (6361 : ZMod 17351)
      decide
    · apply IsUnit.of_mul_eq_one (14773 : ZMod 17351)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_17359 : Nat.Prime 17359 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 17359 17358 1 3 [2, 3, 11, 263]
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
    · apply IsUnit.of_mul_eq_one (8679 : ZMod 17359)
      decide
    · apply IsUnit.of_mul_eq_one (5130 : ZMod 17359)
      decide
    · apply IsUnit.of_mul_eq_one (14631 : ZMod 17359)
      decide
    · apply IsUnit.of_mul_eq_one (12255 : ZMod 17359)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_17377 : Nat.Prime 17377 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 17377 17376 1 7 [2, 2, 2, 2, 2, 3, 181]
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
    · apply IsUnit.of_mul_eq_one (8688 : ZMod 17377)
      decide
    · apply IsUnit.of_mul_eq_one (11165 : ZMod 17377)
      decide
    · apply IsUnit.of_mul_eq_one (4457 : ZMod 17377)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_17383 : Nat.Prime 17383 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 17383 17382 1 5 [2, 3, 2897]
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
    · apply IsUnit.of_mul_eq_one (8691 : ZMod 17383)
      decide
    · apply IsUnit.of_mul_eq_one (1057 : ZMod 17383)
      decide
    · apply IsUnit.of_mul_eq_one (17215 : ZMod 17383)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_17387 : Nat.Prime 17387 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 17387 17386 1 2 [2, 8693]
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
    · apply IsUnit.of_mul_eq_one (8693 : ZMod 17387)
      decide
    · apply IsUnit.of_mul_eq_one (5796 : ZMod 17387)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_17389 : Nat.Prime 17389 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 17389 17388 1 2 [2, 2, 3, 3, 3, 7, 23]
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
    · apply IsUnit.of_mul_eq_one (8694 : ZMod 17389)
      decide
    · apply IsUnit.of_mul_eq_one (10378 : ZMod 17389)
      decide
    · apply IsUnit.of_mul_eq_one (1874 : ZMod 17389)
      decide
    · apply IsUnit.of_mul_eq_one (17385 : ZMod 17389)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_17393 : Nat.Prime 17393 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 17393 17392 1 3 [2, 2, 2, 2, 1087]
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
    · apply IsUnit.of_mul_eq_one (8696 : ZMod 17393)
      decide
    · apply IsUnit.of_mul_eq_one (3770 : ZMod 17393)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_17401 : Nat.Prime 17401 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 17401 17400 1 11 [2, 2, 2, 3, 5, 5, 29]
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
    · apply IsUnit.of_mul_eq_one (8700 : ZMod 17401)
      decide
    · apply IsUnit.of_mul_eq_one (201 : ZMod 17401)
      decide
    · apply IsUnit.of_mul_eq_one (11290 : ZMod 17401)
      decide
    · apply IsUnit.of_mul_eq_one (4786 : ZMod 17401)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_17417 : Nat.Prime 17417 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 17417 17416 1 3 [2, 2, 2, 7, 311]
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
    · apply IsUnit.of_mul_eq_one (8708 : ZMod 17417)
      decide
    · apply IsUnit.of_mul_eq_one (14203 : ZMod 17417)
      decide
    · apply IsUnit.of_mul_eq_one (4925 : ZMod 17417)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_17419 : Nat.Prime 17419 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 17419 17418 1 3 [2, 3, 2903]
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
    · apply IsUnit.of_mul_eq_one (8709 : ZMod 17419)
      decide
    · apply IsUnit.of_mul_eq_one (13842 : ZMod 17419)
      decide
    · apply IsUnit.of_mul_eq_one (6245 : ZMod 17419)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_17431 : Nat.Prime 17431 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 17431 17430 1 3 [2, 3, 5, 7, 83]
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
    · apply IsUnit.of_mul_eq_one (8715 : ZMod 17431)
      decide
    · apply IsUnit.of_mul_eq_one (4815 : ZMod 17431)
      decide
    · apply IsUnit.of_mul_eq_one (15936 : ZMod 17431)
      decide
    · apply IsUnit.of_mul_eq_one (6648 : ZMod 17431)
      decide
    · apply IsUnit.of_mul_eq_one (1033 : ZMod 17431)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_17443 : Nat.Prime 17443 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 17443 17442 1 2 [2, 3, 3, 3, 17, 19]
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
    · apply IsUnit.of_mul_eq_one (8721 : ZMod 17443)
      decide
    · apply IsUnit.of_mul_eq_one (3773 : ZMod 17443)
      decide
    · apply IsUnit.of_mul_eq_one (15897 : ZMod 17443)
      decide
    · apply IsUnit.of_mul_eq_one (5659 : ZMod 17443)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_17449 : Nat.Prime 17449 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 17449 17448 1 14 [2, 2, 2, 3, 727]
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
    · apply IsUnit.of_mul_eq_one (8724 : ZMod 17449)
      decide
    · apply IsUnit.of_mul_eq_one (11900 : ZMod 17449)
      decide
    · apply IsUnit.of_mul_eq_one (10142 : ZMod 17449)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_17467 : Nat.Prime 17467 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 17467 17466 1 3 [2, 3, 41, 71]
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
    · apply IsUnit.of_mul_eq_one (8733 : ZMod 17467)
      decide
    · apply IsUnit.of_mul_eq_one (9347 : ZMod 17467)
      decide
    · apply IsUnit.of_mul_eq_one (1064 : ZMod 17467)
      decide
    · apply IsUnit.of_mul_eq_one (1228 : ZMod 17467)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_17471 : Nat.Prime 17471 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 17471 17470 1 11 [2, 5, 1747]
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
    · apply IsUnit.of_mul_eq_one (8735 : ZMod 17471)
      decide
    · apply IsUnit.of_mul_eq_one (7310 : ZMod 17471)
      decide
    · apply IsUnit.of_mul_eq_one (16225 : ZMod 17471)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_17477 : Nat.Prime 17477 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 17477 17476 1 2 [2, 2, 17, 257]
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
    · apply IsUnit.of_mul_eq_one (8738 : ZMod 17477)
      decide
    · apply IsUnit.of_mul_eq_one (8004 : ZMod 17477)
      decide
    · apply IsUnit.of_mul_eq_one (8236 : ZMod 17477)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_17483 : Nat.Prime 17483 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 17483 17482 1 2 [2, 8741]
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
    · apply IsUnit.of_mul_eq_one (8741 : ZMod 17483)
      decide
    · apply IsUnit.of_mul_eq_one (5828 : ZMod 17483)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_17489 : Nat.Prime 17489 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 17489 17488 1 3 [2, 2, 2, 2, 1093]
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
    · apply IsUnit.of_mul_eq_one (8744 : ZMod 17489)
      decide
    · apply IsUnit.of_mul_eq_one (17350 : ZMod 17489)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_17491 : Nat.Prime 17491 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 17491 17490 1 3 [2, 3, 5, 11, 53]
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
    · apply IsUnit.of_mul_eq_one (8745 : ZMod 17491)
      decide
    · apply IsUnit.of_mul_eq_one (5267 : ZMod 17491)
      decide
    · apply IsUnit.of_mul_eq_one (10184 : ZMod 17491)
      decide
    · apply IsUnit.of_mul_eq_one (10644 : ZMod 17491)
      decide
    · apply IsUnit.of_mul_eq_one (10972 : ZMod 17491)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_17497 : Nat.Prime 17497 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 17497 17496 1 5 [2, 2, 2, 3, 3, 3, 3, 3, 3, 3]
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
    · apply IsUnit.of_mul_eq_one (8748 : ZMod 17497)
      decide
    · apply IsUnit.of_mul_eq_one (10091 : ZMod 17497)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_17509 : Nat.Prime 17509 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 17509 17508 1 2 [2, 2, 3, 1459]
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
    · apply IsUnit.of_mul_eq_one (8754 : ZMod 17509)
      decide
    · apply IsUnit.of_mul_eq_one (4460 : ZMod 17509)
      decide
    · apply IsUnit.of_mul_eq_one (16594 : ZMod 17509)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_17519 : Nat.Prime 17519 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 17519 17518 1 13 [2, 19, 461]
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
    · apply IsUnit.of_mul_eq_one (8759 : ZMod 17519)
      decide
    · apply IsUnit.of_mul_eq_one (16464 : ZMod 17519)
      decide
    · apply IsUnit.of_mul_eq_one (13983 : ZMod 17519)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_17539 : Nat.Prime 17539 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 17539 17538 1 3 [2, 3, 37, 79]
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
    · apply IsUnit.of_mul_eq_one (8769 : ZMod 17539)
      decide
    · apply IsUnit.of_mul_eq_one (11533 : ZMod 17539)
      decide
    · apply IsUnit.of_mul_eq_one (9401 : ZMod 17539)
      decide
    · apply IsUnit.of_mul_eq_one (12534 : ZMod 17539)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_17551 : Nat.Prime 17551 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 17551 17550 1 3 [2, 3, 3, 3, 5, 5, 13]
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
    · apply IsUnit.of_mul_eq_one (8775 : ZMod 17551)
      decide
    · apply IsUnit.of_mul_eq_one (7761 : ZMod 17551)
      decide
    · apply IsUnit.of_mul_eq_one (15663 : ZMod 17551)
      decide
    · apply IsUnit.of_mul_eq_one (14823 : ZMod 17551)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_17569 : Nat.Prime 17569 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 17569 17568 1 11 [2, 2, 2, 2, 2, 3, 3, 61]
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
    · apply IsUnit.of_mul_eq_one (8784 : ZMod 17569)
      decide
    · apply IsUnit.of_mul_eq_one (7540 : ZMod 17569)
      decide
    · apply IsUnit.of_mul_eq_one (6249 : ZMod 17569)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_17573 : Nat.Prime 17573 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 17573 17572 1 2 [2, 2, 23, 191]
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
    · apply IsUnit.of_mul_eq_one (8786 : ZMod 17573)
      decide
    · apply IsUnit.of_mul_eq_one (4240 : ZMod 17573)
      decide
    · apply IsUnit.of_mul_eq_one (16533 : ZMod 17573)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_17579 : Nat.Prime 17579 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 17579 17578 1 2 [2, 11, 17, 47]
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
    · apply IsUnit.of_mul_eq_one (8789 : ZMod 17579)
      decide
    · apply IsUnit.of_mul_eq_one (1505 : ZMod 17579)
      decide
    · apply IsUnit.of_mul_eq_one (3061 : ZMod 17579)
      decide
    · apply IsUnit.of_mul_eq_one (1504 : ZMod 17579)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_17581 : Nat.Prime 17581 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 17581 17580 1 10 [2, 2, 3, 5, 293]
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
    · apply IsUnit.of_mul_eq_one (8790 : ZMod 17581)
      decide
    · apply IsUnit.of_mul_eq_one (15850 : ZMod 17581)
      decide
    · apply IsUnit.of_mul_eq_one (4467 : ZMod 17581)
      decide
    · apply IsUnit.of_mul_eq_one (3624 : ZMod 17581)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_17597 : Nat.Prime 17597 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 17597 17596 1 2 [2, 2, 53, 83]
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
    · apply IsUnit.of_mul_eq_one (8798 : ZMod 17597)
      decide
    · apply IsUnit.of_mul_eq_one (14545 : ZMod 17597)
      decide
    · apply IsUnit.of_mul_eq_one (7039 : ZMod 17597)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_17599 : Nat.Prime 17599 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 17599 17598 1 6 [2, 3, 7, 419]
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
    · apply IsUnit.of_mul_eq_one (8799 : ZMod 17599)
      decide
    · apply IsUnit.of_mul_eq_one (8128 : ZMod 17599)
      decide
    · apply IsUnit.of_mul_eq_one (9114 : ZMod 17599)
      decide
    · apply IsUnit.of_mul_eq_one (7240 : ZMod 17599)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_17609 : Nat.Prime 17609 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 17609 17608 1 3 [2, 2, 2, 31, 71]
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
    · apply IsUnit.of_mul_eq_one (8804 : ZMod 17609)
      decide
    · apply IsUnit.of_mul_eq_one (11613 : ZMod 17609)
      decide
    · apply IsUnit.of_mul_eq_one (10622 : ZMod 17609)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_17623 : Nat.Prime 17623 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 17623 17622 1 3 [2, 3, 3, 11, 89]
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
    · apply IsUnit.of_mul_eq_one (8811 : ZMod 17623)
      decide
    · apply IsUnit.of_mul_eq_one (4757 : ZMod 17623)
      decide
    · apply IsUnit.of_mul_eq_one (17293 : ZMod 17623)
      decide
    · apply IsUnit.of_mul_eq_one (12378 : ZMod 17623)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_17627 : Nat.Prime 17627 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 17627 17626 1 2 [2, 7, 1259]
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
    · apply IsUnit.of_mul_eq_one (8813 : ZMod 17627)
      decide
    · apply IsUnit.of_mul_eq_one (14848 : ZMod 17627)
      decide
    · apply IsUnit.of_mul_eq_one (4010 : ZMod 17627)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_17657 : Nat.Prime 17657 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 17657 17656 1 3 [2, 2, 2, 2207]
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
    · apply IsUnit.of_mul_eq_one (8828 : ZMod 17657)
      decide
    · apply IsUnit.of_mul_eq_one (9278 : ZMod 17657)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_17659 : Nat.Prime 17659 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 17659 17658 1 3 [2, 3, 3, 3, 3, 109]
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
    · apply IsUnit.of_mul_eq_one (8829 : ZMod 17659)
      decide
    · apply IsUnit.of_mul_eq_one (8515 : ZMod 17659)
      decide
    · apply IsUnit.of_mul_eq_one (15537 : ZMod 17659)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_17669 : Nat.Prime 17669 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 17669 17668 1 2 [2, 2, 7, 631]
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
    · apply IsUnit.of_mul_eq_one (8834 : ZMod 17669)
      decide
    · apply IsUnit.of_mul_eq_one (2582 : ZMod 17669)
      decide
    · apply IsUnit.of_mul_eq_one (13911 : ZMod 17669)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_17681 : Nat.Prime 17681 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 17681 17680 1 3 [2, 2, 2, 2, 5, 13, 17]
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
    · apply IsUnit.of_mul_eq_one (8840 : ZMod 17681)
      decide
    · apply IsUnit.of_mul_eq_one (2155 : ZMod 17681)
      decide
    · apply IsUnit.of_mul_eq_one (15632 : ZMod 17681)
      decide
    · apply IsUnit.of_mul_eq_one (6294 : ZMod 17681)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_17683 : Nat.Prime 17683 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 17683 17682 1 5 [2, 3, 7, 421]
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
    · apply IsUnit.of_mul_eq_one (8841 : ZMod 17683)
      decide
    · apply IsUnit.of_mul_eq_one (13145 : ZMod 17683)
      decide
    · apply IsUnit.of_mul_eq_one (6362 : ZMod 17683)
      decide
    · apply IsUnit.of_mul_eq_one (10940 : ZMod 17683)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_17707 : Nat.Prime 17707 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 17707 17706 1 3 [2, 3, 13, 227]
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
    · apply IsUnit.of_mul_eq_one (8853 : ZMod 17707)
      decide
    · apply IsUnit.of_mul_eq_one (4357 : ZMod 17707)
      decide
    · apply IsUnit.of_mul_eq_one (1576 : ZMod 17707)
      decide
    · apply IsUnit.of_mul_eq_one (10028 : ZMod 17707)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_17713 : Nat.Prime 17713 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 17713 17712 1 7 [2, 2, 2, 2, 3, 3, 3, 41]
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
    · apply IsUnit.of_mul_eq_one (8856 : ZMod 17713)
      decide
    · apply IsUnit.of_mul_eq_one (2122 : ZMod 17713)
      decide
    · apply IsUnit.of_mul_eq_one (4578 : ZMod 17713)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_17729 : Nat.Prime 17729 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 17729 17728 1 3 [2, 2, 2, 2, 2, 2, 277]
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
    rcases hq with rfl | rfl
    · apply IsUnit.of_mul_eq_one (8864 : ZMod 17729)
      decide
    · apply IsUnit.of_mul_eq_one (3694 : ZMod 17729)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_17737 : Nat.Prime 17737 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 17737 17736 1 7 [2, 2, 2, 3, 739]
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
    · apply IsUnit.of_mul_eq_one (8868 : ZMod 17737)
      decide
    · apply IsUnit.of_mul_eq_one (17003 : ZMod 17737)
      decide
    · apply IsUnit.of_mul_eq_one (4746 : ZMod 17737)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_17747 : Nat.Prime 17747 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 17747 17746 1 2 [2, 19, 467]
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
    · apply IsUnit.of_mul_eq_one (8873 : ZMod 17747)
      decide
    · apply IsUnit.of_mul_eq_one (16497 : ZMod 17747)
      decide
    · apply IsUnit.of_mul_eq_one (2170 : ZMod 17747)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_17749 : Nat.Prime 17749 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 17749 17748 1 2 [2, 2, 3, 3, 17, 29]
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
    · apply IsUnit.of_mul_eq_one (8874 : ZMod 17749)
      decide
    · apply IsUnit.of_mul_eq_one (14158 : ZMod 17749)
      decide
    · apply IsUnit.of_mul_eq_one (5880 : ZMod 17749)
      decide
    · apply IsUnit.of_mul_eq_one (9713 : ZMod 17749)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_17761 : Nat.Prime 17761 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 17761 17760 1 19 [2, 2, 2, 2, 2, 3, 5, 37]
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
    · apply IsUnit.of_mul_eq_one (8880 : ZMod 17761)
      decide
    · apply IsUnit.of_mul_eq_one (945 : ZMod 17761)
      decide
    · apply IsUnit.of_mul_eq_one (10963 : ZMod 17761)
      decide
    · apply IsUnit.of_mul_eq_one (3018 : ZMod 17761)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_17783 : Nat.Prime 17783 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 17783 17782 1 5 [2, 17, 523]
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
    · apply IsUnit.of_mul_eq_one (8891 : ZMod 17783)
      decide
    · apply IsUnit.of_mul_eq_one (13953 : ZMod 17783)
      decide
    · apply IsUnit.of_mul_eq_one (7995 : ZMod 17783)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_17789 : Nat.Prime 17789 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 17789 17788 1 2 [2, 2, 4447]
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
    · apply IsUnit.of_mul_eq_one (8894 : ZMod 17789)
      decide
    · apply IsUnit.of_mul_eq_one (1186 : ZMod 17789)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_17791 : Nat.Prime 17791 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 17791 17790 1 3 [2, 3, 5, 593]
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
    · apply IsUnit.of_mul_eq_one (8895 : ZMod 17791)
      decide
    · apply IsUnit.of_mul_eq_one (4428 : ZMod 17791)
      decide
    · apply IsUnit.of_mul_eq_one (5012 : ZMod 17791)
      decide
    · apply IsUnit.of_mul_eq_one (3884 : ZMod 17791)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_17807 : Nat.Prime 17807 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 17807 17806 1 5 [2, 29, 307]
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
    · apply IsUnit.of_mul_eq_one (8903 : ZMod 17807)
      decide
    · apply IsUnit.of_mul_eq_one (11073 : ZMod 17807)
      decide
    · apply IsUnit.of_mul_eq_one (12899 : ZMod 17807)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_17827 : Nat.Prime 17827 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 17827 17826 1 2 [2, 3, 2971]
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
    · apply IsUnit.of_mul_eq_one (8913 : ZMod 17827)
      decide
    · apply IsUnit.of_mul_eq_one (5314 : ZMod 17827)
      decide
    · apply IsUnit.of_mul_eq_one (9055 : ZMod 17827)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_17837 : Nat.Prime 17837 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 17837 17836 1 2 [2, 2, 7, 7, 7, 13]
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
    · apply IsUnit.of_mul_eq_one (8918 : ZMod 17837)
      decide
    · apply IsUnit.of_mul_eq_one (7885 : ZMod 17837)
      decide
    · apply IsUnit.of_mul_eq_one (2230 : ZMod 17837)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_17839 : Nat.Prime 17839 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 17839 17838 1 6 [2, 3, 3, 991]
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
    · apply IsUnit.of_mul_eq_one (8919 : ZMod 17839)
      decide
    · apply IsUnit.of_mul_eq_one (16075 : ZMod 17839)
      decide
    · apply IsUnit.of_mul_eq_one (17129 : ZMod 17839)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_17851 : Nat.Prime 17851 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 17851 17850 1 2 [2, 3, 5, 5, 7, 17]
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
    · apply IsUnit.of_mul_eq_one (8925 : ZMod 17851)
      decide
    · apply IsUnit.of_mul_eq_one (16730 : ZMod 17851)
      decide
    · apply IsUnit.of_mul_eq_one (2339 : ZMod 17851)
      decide
    · apply IsUnit.of_mul_eq_one (6976 : ZMod 17851)
      decide
    · apply IsUnit.of_mul_eq_one (5078 : ZMod 17851)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_17863 : Nat.Prime 17863 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 17863 17862 1 6 [2, 3, 13, 229]
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
    · apply IsUnit.of_mul_eq_one (8931 : ZMod 17863)
      decide
    · apply IsUnit.of_mul_eq_one (9184 : ZMod 17863)
      decide
    · apply IsUnit.of_mul_eq_one (11702 : ZMod 17863)
      decide
    · apply IsUnit.of_mul_eq_one (837 : ZMod 17863)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_17881 : Nat.Prime 17881 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 17881 17880 1 7 [2, 2, 2, 3, 5, 149]
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
    · apply IsUnit.of_mul_eq_one (8940 : ZMod 17881)
      decide
    · apply IsUnit.of_mul_eq_one (13780 : ZMod 17881)
      decide
    · apply IsUnit.of_mul_eq_one (6375 : ZMod 17881)
      decide
    · apply IsUnit.of_mul_eq_one (15183 : ZMod 17881)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_17891 : Nat.Prime 17891 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 17891 17890 1 2 [2, 5, 1789]
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
    · apply IsUnit.of_mul_eq_one (8945 : ZMod 17891)
      decide
    · apply IsUnit.of_mul_eq_one (13914 : ZMod 17891)
      decide
    · apply IsUnit.of_mul_eq_one (3113 : ZMod 17891)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_17903 : Nat.Prime 17903 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 17903 17902 1 5 [2, 8951]
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
    · apply IsUnit.of_mul_eq_one (8951 : ZMod 17903)
      decide
    · apply IsUnit.of_mul_eq_one (746 : ZMod 17903)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_17909 : Nat.Prime 17909 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 17909 17908 1 2 [2, 2, 11, 11, 37]
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
    · apply IsUnit.of_mul_eq_one (8954 : ZMod 17909)
      decide
    · apply IsUnit.of_mul_eq_one (9684 : ZMod 17909)
      decide
    · apply IsUnit.of_mul_eq_one (10438 : ZMod 17909)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_17911 : Nat.Prime 17911 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 17911 17910 1 3 [2, 3, 3, 5, 199]
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
    · apply IsUnit.of_mul_eq_one (8955 : ZMod 17911)
      decide
    · apply IsUnit.of_mul_eq_one (13623 : ZMod 17911)
      decide
    · apply IsUnit.of_mul_eq_one (7261 : ZMod 17911)
      decide
    · apply IsUnit.of_mul_eq_one (4038 : ZMod 17911)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_17921 : Nat.Prime 17921 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 17921 17920 1 3 [2, 2, 2, 2, 2, 2, 2, 2, 2, 5, 7]
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
    · apply IsUnit.of_mul_eq_one (8960 : ZMod 17921)
      decide
    · apply IsUnit.of_mul_eq_one (10503 : ZMod 17921)
      decide
    · apply IsUnit.of_mul_eq_one (12499 : ZMod 17921)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_17923 : Nat.Prime 17923 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 17923 17922 1 2 [2, 3, 29, 103]
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
    · apply IsUnit.of_mul_eq_one (8961 : ZMod 17923)
      decide
    · apply IsUnit.of_mul_eq_one (204 : ZMod 17923)
      decide
    · apply IsUnit.of_mul_eq_one (3102 : ZMod 17923)
      decide
    · apply IsUnit.of_mul_eq_one (1634 : ZMod 17923)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_17929 : Nat.Prime 17929 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 17929 17928 1 11 [2, 2, 2, 3, 3, 3, 83]
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
    · apply IsUnit.of_mul_eq_one (8964 : ZMod 17929)
      decide
    · apply IsUnit.of_mul_eq_one (6911 : ZMod 17929)
      decide
    · apply IsUnit.of_mul_eq_one (841 : ZMod 17929)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_18839 : Nat.Prime 18839 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 18839 18838 1 7 [2, 9419]
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
    · apply IsUnit.of_mul_eq_one (9419 : ZMod 18839)
      decide
    · apply IsUnit.of_mul_eq_one (9812 : ZMod 18839)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_18859 : Nat.Prime 18859 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 18859 18858 1 2 [2, 3, 7, 449]
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
    · apply IsUnit.of_mul_eq_one (9429 : ZMod 18859)
      decide
    · apply IsUnit.of_mul_eq_one (7141 : ZMod 18859)
      decide
    · apply IsUnit.of_mul_eq_one (14750 : ZMod 18859)
      decide
    · apply IsUnit.of_mul_eq_one (4694 : ZMod 18859)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_18869 : Nat.Prime 18869 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 18869 18868 1 2 [2, 2, 53, 89]
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
    · apply IsUnit.of_mul_eq_one (9434 : ZMod 18869)
      decide
    · apply IsUnit.of_mul_eq_one (12409 : ZMod 18869)
      decide
    · apply IsUnit.of_mul_eq_one (17623 : ZMod 18869)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_18899 : Nat.Prime 18899 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 18899 18898 1 2 [2, 11, 859]
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
    · apply IsUnit.of_mul_eq_one (9449 : ZMod 18899)
      decide
    · apply IsUnit.of_mul_eq_one (16746 : ZMod 18899)
      decide
    · apply IsUnit.of_mul_eq_one (4432 : ZMod 18899)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_18911 : Nat.Prime 18911 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 18911 18910 1 14 [2, 5, 31, 61]
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
    · apply IsUnit.of_mul_eq_one (9455 : ZMod 18911)
      decide
    · apply IsUnit.of_mul_eq_one (4322 : ZMod 18911)
      decide
    · apply IsUnit.of_mul_eq_one (14786 : ZMod 18911)
      decide
    · apply IsUnit.of_mul_eq_one (17232 : ZMod 18911)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_18913 : Nat.Prime 18913 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 18913 18912 1 7 [2, 2, 2, 2, 2, 3, 197]
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
    · apply IsUnit.of_mul_eq_one (9456 : ZMod 18913)
      decide
    · apply IsUnit.of_mul_eq_one (10522 : ZMod 18913)
      decide
    · apply IsUnit.of_mul_eq_one (5798 : ZMod 18913)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_18917 : Nat.Prime 18917 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 18917 18916 1 2 [2, 2, 4729]
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
    · apply IsUnit.of_mul_eq_one (9458 : ZMod 18917)
      decide
    · apply IsUnit.of_mul_eq_one (8828 : ZMod 18917)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_18919 : Nat.Prime 18919 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 18919 18918 1 3 [2, 3, 3, 1051]
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
    · apply IsUnit.of_mul_eq_one (9459 : ZMod 18919)
      decide
    · apply IsUnit.of_mul_eq_one (18240 : ZMod 18919)
      decide
    · apply IsUnit.of_mul_eq_one (5803 : ZMod 18919)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_18947 : Nat.Prime 18947 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 18947 18946 1 2 [2, 9473]
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
    · apply IsUnit.of_mul_eq_one (9473 : ZMod 18947)
      decide
    · apply IsUnit.of_mul_eq_one (6316 : ZMod 18947)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_18959 : Nat.Prime 18959 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 18959 18958 1 13 [2, 9479]
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
    · apply IsUnit.of_mul_eq_one (9479 : ZMod 18959)
      decide
    · apply IsUnit.of_mul_eq_one (13655 : ZMod 18959)
      decide
  · norm_num
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_18041_18958_part11 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_18958 (p := 18803) (q := 18839) (by exact lowPrime_18839) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18958 (p := 18839) (q := 18859) (by exact lowPrime_18859) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18958 (p := 18859) (q := 18869) (by exact lowPrime_18869) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18958 (p := 18869) (q := 18899) (by exact lowPrime_18899) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18958 (p := 18899) (q := 18911) (by exact lowPrime_18911) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18958 (p := 18911) (q := 18913) (by exact lowPrime_18913) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18958 (p := 18913) (q := 18917) (by exact lowPrime_18917) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18958 (p := 18917) (q := 18919) (by exact lowPrime_18919) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_18041_18958_part11_chain :
    DusartPrimeRowsChain 18803 18918 dusartPrimeRows_18041_18958_part11 := by
  apply DusartPrimeRowsChain.cons
  · norm_num [dusartPrimeRow_of_explicit_18958]
  · norm_num [dusartPrimeRow_of_explicit_18958]
  · apply DusartPrimeRowsChain.cons
    · norm_num [dusartPrimeRow_of_explicit_18958]
    · norm_num [dusartPrimeRow_of_explicit_18958]
    · apply DusartPrimeRowsChain.cons
      · norm_num [dusartPrimeRow_of_explicit_18958]
      · norm_num [dusartPrimeRow_of_explicit_18958]
      · apply DusartPrimeRowsChain.cons
        · norm_num [dusartPrimeRow_of_explicit_18958]
        · norm_num [dusartPrimeRow_of_explicit_18958]
        · apply DusartPrimeRowsChain.cons
          · norm_num [dusartPrimeRow_of_explicit_18958]
          · norm_num [dusartPrimeRow_of_explicit_18958]
          · apply DusartPrimeRowsChain.cons
            · norm_num [dusartPrimeRow_of_explicit_18958]
            · norm_num [dusartPrimeRow_of_explicit_18958]
            · apply DusartPrimeRowsChain.cons
              · norm_num [dusartPrimeRow_of_explicit_18958]
              · norm_num [dusartPrimeRow_of_explicit_18958]
              · apply DusartPrimeRowsChain.cons
                · norm_num [dusartPrimeRow_of_explicit_18958]
                · norm_num [dusartPrimeRow_of_explicit_18958]
                · apply DusartPrimeRowsChain.empty
                  norm_num [dusartPrimeRow_of_explicit_18958, dusartPrimeRow_of_explicit_right]

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_18041_18958_part12 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_18958 (p := 18919) (q := 18947) (by exact lowPrime_18947) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18958 (p := 18947) (q := 18959) (by exact lowPrime_18959) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_18041_18958_part12_chain :
    DusartPrimeRowsChain 18919 18958 dusartPrimeRows_18041_18958_part12 := by
  apply DusartPrimeRowsChain.cons
  · norm_num [dusartPrimeRow_of_explicit_18958]
  · norm_num [dusartPrimeRow_of_explicit_18958]
  · apply DusartPrimeRowsChain.cons
    · norm_num [dusartPrimeRow_of_explicit_18958]
    · norm_num [dusartPrimeRow_of_explicit_18958]
    · apply DusartPrimeRowsChain.empty
      norm_num [dusartPrimeRow_of_explicit_18958, dusartPrimeRow_of_explicit_right]

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_17159_18040_part01 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_18033 (p := 17159) (q := 17167) (by exact lowPrime_17167) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18033 (p := 17167) (q := 17183) (by exact lowPrime_17183) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18033 (p := 17183) (q := 17189) (by exact lowPrime_17189) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18033 (p := 17189) (q := 17191) (by exact lowPrime_17191) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18033 (p := 17191) (q := 17203) (by exact lowPrime_17203) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18033 (p := 17203) (q := 17207) (by exact lowPrime_17207) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18033 (p := 17207) (q := 17209) (by exact lowPrime_17209) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18033 (p := 17209) (q := 17231) (by exact lowPrime_17231) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_17159_18040_part01_chain :
    DusartPrimeRowsChain 17159 17230 dusartPrimeRows_17159_18040_part01 := by
  apply DusartPrimeRowsChain.cons
  · norm_num [dusartPrimeRow_of_explicit_18033]
  · norm_num [dusartPrimeRow_of_explicit_18033]
  · apply DusartPrimeRowsChain.cons
    · norm_num [dusartPrimeRow_of_explicit_18033]
    · norm_num [dusartPrimeRow_of_explicit_18033]
    · apply DusartPrimeRowsChain.cons
      · norm_num [dusartPrimeRow_of_explicit_18033]
      · norm_num [dusartPrimeRow_of_explicit_18033]
      · apply DusartPrimeRowsChain.cons
        · norm_num [dusartPrimeRow_of_explicit_18033]
        · norm_num [dusartPrimeRow_of_explicit_18033]
        · apply DusartPrimeRowsChain.cons
          · norm_num [dusartPrimeRow_of_explicit_18033]
          · norm_num [dusartPrimeRow_of_explicit_18033]
          · apply DusartPrimeRowsChain.cons
            · norm_num [dusartPrimeRow_of_explicit_18033]
            · norm_num [dusartPrimeRow_of_explicit_18033]
            · apply DusartPrimeRowsChain.cons
              · norm_num [dusartPrimeRow_of_explicit_18033]
              · norm_num [dusartPrimeRow_of_explicit_18033]
              · apply DusartPrimeRowsChain.cons
                · norm_num [dusartPrimeRow_of_explicit_18033]
                · norm_num [dusartPrimeRow_of_explicit_18033]
                · apply DusartPrimeRowsChain.empty
                  norm_num [dusartPrimeRow_of_explicit_18033, dusartPrimeRow_of_explicit_right]

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_17159_18040_part02 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_18033 (p := 17231) (q := 17239) (by exact lowPrime_17239) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18033 (p := 17239) (q := 17257) (by exact lowPrime_17257) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18033 (p := 17257) (q := 17291) (by exact lowPrime_17291) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18033 (p := 17291) (q := 17293) (by exact lowPrime_17293) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18033 (p := 17293) (q := 17299) (by exact lowPrime_17299) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18033 (p := 17299) (q := 17317) (by exact lowPrime_17317) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18033 (p := 17317) (q := 17321) (by exact lowPrime_17321) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18033 (p := 17321) (q := 17327) (by exact lowPrime_17327) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_17159_18040_part02_chain :
    DusartPrimeRowsChain 17231 17326 dusartPrimeRows_17159_18040_part02 := by
  apply DusartPrimeRowsChain.cons
  · norm_num [dusartPrimeRow_of_explicit_18033]
  · norm_num [dusartPrimeRow_of_explicit_18033]
  · apply DusartPrimeRowsChain.cons
    · norm_num [dusartPrimeRow_of_explicit_18033]
    · norm_num [dusartPrimeRow_of_explicit_18033]
    · apply DusartPrimeRowsChain.cons
      · norm_num [dusartPrimeRow_of_explicit_18033]
      · norm_num [dusartPrimeRow_of_explicit_18033]
      · apply DusartPrimeRowsChain.cons
        · norm_num [dusartPrimeRow_of_explicit_18033]
        · norm_num [dusartPrimeRow_of_explicit_18033]
        · apply DusartPrimeRowsChain.cons
          · norm_num [dusartPrimeRow_of_explicit_18033]
          · norm_num [dusartPrimeRow_of_explicit_18033]
          · apply DusartPrimeRowsChain.cons
            · norm_num [dusartPrimeRow_of_explicit_18033]
            · norm_num [dusartPrimeRow_of_explicit_18033]
            · apply DusartPrimeRowsChain.cons
              · norm_num [dusartPrimeRow_of_explicit_18033]
              · norm_num [dusartPrimeRow_of_explicit_18033]
              · apply DusartPrimeRowsChain.cons
                · norm_num [dusartPrimeRow_of_explicit_18033]
                · norm_num [dusartPrimeRow_of_explicit_18033]
                · apply DusartPrimeRowsChain.empty
                  norm_num [dusartPrimeRow_of_explicit_18033, dusartPrimeRow_of_explicit_right]

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_17159_18040_part03 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_18033 (p := 17327) (q := 17333) (by exact lowPrime_17333) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18033 (p := 17333) (q := 17341) (by exact lowPrime_17341) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18033 (p := 17341) (q := 17351) (by exact lowPrime_17351) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18033 (p := 17351) (q := 17359) (by exact lowPrime_17359) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18033 (p := 17359) (q := 17377) (by exact lowPrime_17377) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18033 (p := 17377) (q := 17383) (by exact lowPrime_17383) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18033 (p := 17383) (q := 17387) (by exact lowPrime_17387) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18033 (p := 17387) (q := 17389) (by exact lowPrime_17389) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_17159_18040_part03_chain :
    DusartPrimeRowsChain 17327 17388 dusartPrimeRows_17159_18040_part03 := by
  apply DusartPrimeRowsChain.cons
  · norm_num [dusartPrimeRow_of_explicit_18033]
  · norm_num [dusartPrimeRow_of_explicit_18033]
  · apply DusartPrimeRowsChain.cons
    · norm_num [dusartPrimeRow_of_explicit_18033]
    · norm_num [dusartPrimeRow_of_explicit_18033]
    · apply DusartPrimeRowsChain.cons
      · norm_num [dusartPrimeRow_of_explicit_18033]
      · norm_num [dusartPrimeRow_of_explicit_18033]
      · apply DusartPrimeRowsChain.cons
        · norm_num [dusartPrimeRow_of_explicit_18033]
        · norm_num [dusartPrimeRow_of_explicit_18033]
        · apply DusartPrimeRowsChain.cons
          · norm_num [dusartPrimeRow_of_explicit_18033]
          · norm_num [dusartPrimeRow_of_explicit_18033]
          · apply DusartPrimeRowsChain.cons
            · norm_num [dusartPrimeRow_of_explicit_18033]
            · norm_num [dusartPrimeRow_of_explicit_18033]
            · apply DusartPrimeRowsChain.cons
              · norm_num [dusartPrimeRow_of_explicit_18033]
              · norm_num [dusartPrimeRow_of_explicit_18033]
              · apply DusartPrimeRowsChain.cons
                · norm_num [dusartPrimeRow_of_explicit_18033]
                · norm_num [dusartPrimeRow_of_explicit_18033]
                · apply DusartPrimeRowsChain.empty
                  norm_num [dusartPrimeRow_of_explicit_18033, dusartPrimeRow_of_explicit_right]

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_17159_18040_part04 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_18033 (p := 17389) (q := 17393) (by exact lowPrime_17393) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18033 (p := 17393) (q := 17401) (by exact lowPrime_17401) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18033 (p := 17401) (q := 17417) (by exact lowPrime_17417) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18033 (p := 17417) (q := 17419) (by exact lowPrime_17419) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18033 (p := 17419) (q := 17431) (by exact lowPrime_17431) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18033 (p := 17431) (q := 17443) (by exact lowPrime_17443) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18033 (p := 17443) (q := 17449) (by exact lowPrime_17449) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18033 (p := 17449) (q := 17467) (by exact lowPrime_17467) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_17159_18040_part04_chain :
    DusartPrimeRowsChain 17389 17466 dusartPrimeRows_17159_18040_part04 := by
  apply DusartPrimeRowsChain.cons
  · norm_num [dusartPrimeRow_of_explicit_18033]
  · norm_num [dusartPrimeRow_of_explicit_18033]
  · apply DusartPrimeRowsChain.cons
    · norm_num [dusartPrimeRow_of_explicit_18033]
    · norm_num [dusartPrimeRow_of_explicit_18033]
    · apply DusartPrimeRowsChain.cons
      · norm_num [dusartPrimeRow_of_explicit_18033]
      · norm_num [dusartPrimeRow_of_explicit_18033]
      · apply DusartPrimeRowsChain.cons
        · norm_num [dusartPrimeRow_of_explicit_18033]
        · norm_num [dusartPrimeRow_of_explicit_18033]
        · apply DusartPrimeRowsChain.cons
          · norm_num [dusartPrimeRow_of_explicit_18033]
          · norm_num [dusartPrimeRow_of_explicit_18033]
          · apply DusartPrimeRowsChain.cons
            · norm_num [dusartPrimeRow_of_explicit_18033]
            · norm_num [dusartPrimeRow_of_explicit_18033]
            · apply DusartPrimeRowsChain.cons
              · norm_num [dusartPrimeRow_of_explicit_18033]
              · norm_num [dusartPrimeRow_of_explicit_18033]
              · apply DusartPrimeRowsChain.cons
                · norm_num [dusartPrimeRow_of_explicit_18033]
                · norm_num [dusartPrimeRow_of_explicit_18033]
                · apply DusartPrimeRowsChain.empty
                  norm_num [dusartPrimeRow_of_explicit_18033, dusartPrimeRow_of_explicit_right]

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_17159_18040_part05 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_18033 (p := 17467) (q := 17471) (by exact lowPrime_17471) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18033 (p := 17471) (q := 17477) (by exact lowPrime_17477) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18033 (p := 17477) (q := 17483) (by exact lowPrime_17483) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18033 (p := 17483) (q := 17489) (by exact lowPrime_17489) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18033 (p := 17489) (q := 17491) (by exact lowPrime_17491) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18033 (p := 17491) (q := 17497) (by exact lowPrime_17497) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18033 (p := 17497) (q := 17509) (by exact lowPrime_17509) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18033 (p := 17509) (q := 17519) (by exact lowPrime_17519) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_17159_18040_part05_chain :
    DusartPrimeRowsChain 17467 17518 dusartPrimeRows_17159_18040_part05 := by
  apply DusartPrimeRowsChain.cons
  · norm_num [dusartPrimeRow_of_explicit_18033]
  · norm_num [dusartPrimeRow_of_explicit_18033]
  · apply DusartPrimeRowsChain.cons
    · norm_num [dusartPrimeRow_of_explicit_18033]
    · norm_num [dusartPrimeRow_of_explicit_18033]
    · apply DusartPrimeRowsChain.cons
      · norm_num [dusartPrimeRow_of_explicit_18033]
      · norm_num [dusartPrimeRow_of_explicit_18033]
      · apply DusartPrimeRowsChain.cons
        · norm_num [dusartPrimeRow_of_explicit_18033]
        · norm_num [dusartPrimeRow_of_explicit_18033]
        · apply DusartPrimeRowsChain.cons
          · norm_num [dusartPrimeRow_of_explicit_18033]
          · norm_num [dusartPrimeRow_of_explicit_18033]
          · apply DusartPrimeRowsChain.cons
            · norm_num [dusartPrimeRow_of_explicit_18033]
            · norm_num [dusartPrimeRow_of_explicit_18033]
            · apply DusartPrimeRowsChain.cons
              · norm_num [dusartPrimeRow_of_explicit_18033]
              · norm_num [dusartPrimeRow_of_explicit_18033]
              · apply DusartPrimeRowsChain.cons
                · norm_num [dusartPrimeRow_of_explicit_18033]
                · norm_num [dusartPrimeRow_of_explicit_18033]
                · apply DusartPrimeRowsChain.empty
                  norm_num [dusartPrimeRow_of_explicit_18033, dusartPrimeRow_of_explicit_right]

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_17159_18040_part06 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_18033 (p := 17519) (q := 17539) (by exact lowPrime_17539) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18033 (p := 17539) (q := 17551) (by exact lowPrime_17551) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18033 (p := 17551) (q := 17569) (by exact lowPrime_17569) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18033 (p := 17569) (q := 17573) (by exact lowPrime_17573) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18033 (p := 17573) (q := 17579) (by exact lowPrime_17579) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18033 (p := 17579) (q := 17581) (by exact lowPrime_17581) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18033 (p := 17581) (q := 17597) (by exact lowPrime_17597) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18033 (p := 17597) (q := 17599) (by exact lowPrime_17599) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_17159_18040_part06_chain :
    DusartPrimeRowsChain 17519 17598 dusartPrimeRows_17159_18040_part06 := by
  apply DusartPrimeRowsChain.cons
  · norm_num [dusartPrimeRow_of_explicit_18033]
  · norm_num [dusartPrimeRow_of_explicit_18033]
  · apply DusartPrimeRowsChain.cons
    · norm_num [dusartPrimeRow_of_explicit_18033]
    · norm_num [dusartPrimeRow_of_explicit_18033]
    · apply DusartPrimeRowsChain.cons
      · norm_num [dusartPrimeRow_of_explicit_18033]
      · norm_num [dusartPrimeRow_of_explicit_18033]
      · apply DusartPrimeRowsChain.cons
        · norm_num [dusartPrimeRow_of_explicit_18033]
        · norm_num [dusartPrimeRow_of_explicit_18033]
        · apply DusartPrimeRowsChain.cons
          · norm_num [dusartPrimeRow_of_explicit_18033]
          · norm_num [dusartPrimeRow_of_explicit_18033]
          · apply DusartPrimeRowsChain.cons
            · norm_num [dusartPrimeRow_of_explicit_18033]
            · norm_num [dusartPrimeRow_of_explicit_18033]
            · apply DusartPrimeRowsChain.cons
              · norm_num [dusartPrimeRow_of_explicit_18033]
              · norm_num [dusartPrimeRow_of_explicit_18033]
              · apply DusartPrimeRowsChain.cons
                · norm_num [dusartPrimeRow_of_explicit_18033]
                · norm_num [dusartPrimeRow_of_explicit_18033]
                · apply DusartPrimeRowsChain.empty
                  norm_num [dusartPrimeRow_of_explicit_18033, dusartPrimeRow_of_explicit_right]

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_17159_18040_part07 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_18033 (p := 17599) (q := 17609) (by exact lowPrime_17609) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18033 (p := 17609) (q := 17623) (by exact lowPrime_17623) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18033 (p := 17623) (q := 17627) (by exact lowPrime_17627) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18033 (p := 17627) (q := 17657) (by exact lowPrime_17657) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18033 (p := 17657) (q := 17659) (by exact lowPrime_17659) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18033 (p := 17659) (q := 17669) (by exact lowPrime_17669) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18033 (p := 17669) (q := 17681) (by exact lowPrime_17681) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18033 (p := 17681) (q := 17683) (by exact lowPrime_17683) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_17159_18040_part07_chain :
    DusartPrimeRowsChain 17599 17682 dusartPrimeRows_17159_18040_part07 := by
  apply DusartPrimeRowsChain.cons
  · norm_num [dusartPrimeRow_of_explicit_18033]
  · norm_num [dusartPrimeRow_of_explicit_18033]
  · apply DusartPrimeRowsChain.cons
    · norm_num [dusartPrimeRow_of_explicit_18033]
    · norm_num [dusartPrimeRow_of_explicit_18033]
    · apply DusartPrimeRowsChain.cons
      · norm_num [dusartPrimeRow_of_explicit_18033]
      · norm_num [dusartPrimeRow_of_explicit_18033]
      · apply DusartPrimeRowsChain.cons
        · norm_num [dusartPrimeRow_of_explicit_18033]
        · norm_num [dusartPrimeRow_of_explicit_18033]
        · apply DusartPrimeRowsChain.cons
          · norm_num [dusartPrimeRow_of_explicit_18033]
          · norm_num [dusartPrimeRow_of_explicit_18033]
          · apply DusartPrimeRowsChain.cons
            · norm_num [dusartPrimeRow_of_explicit_18033]
            · norm_num [dusartPrimeRow_of_explicit_18033]
            · apply DusartPrimeRowsChain.cons
              · norm_num [dusartPrimeRow_of_explicit_18033]
              · norm_num [dusartPrimeRow_of_explicit_18033]
              · apply DusartPrimeRowsChain.cons
                · norm_num [dusartPrimeRow_of_explicit_18033]
                · norm_num [dusartPrimeRow_of_explicit_18033]
                · apply DusartPrimeRowsChain.empty
                  norm_num [dusartPrimeRow_of_explicit_18033, dusartPrimeRow_of_explicit_right]

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_17159_18040_part08 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_18033 (p := 17683) (q := 17707) (by exact lowPrime_17707) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18033 (p := 17707) (q := 17713) (by exact lowPrime_17713) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18033 (p := 17713) (q := 17729) (by exact lowPrime_17729) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18033 (p := 17729) (q := 17737) (by exact lowPrime_17737) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18033 (p := 17737) (q := 17747) (by exact lowPrime_17747) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18033 (p := 17747) (q := 17749) (by exact lowPrime_17749) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18033 (p := 17749) (q := 17761) (by exact lowPrime_17761) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18033 (p := 17761) (q := 17783) (by exact lowPrime_17783) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_17159_18040_part08_chain :
    DusartPrimeRowsChain 17683 17782 dusartPrimeRows_17159_18040_part08 := by
  apply DusartPrimeRowsChain.cons
  · norm_num [dusartPrimeRow_of_explicit_18033]
  · norm_num [dusartPrimeRow_of_explicit_18033]
  · apply DusartPrimeRowsChain.cons
    · norm_num [dusartPrimeRow_of_explicit_18033]
    · norm_num [dusartPrimeRow_of_explicit_18033]
    · apply DusartPrimeRowsChain.cons
      · norm_num [dusartPrimeRow_of_explicit_18033]
      · norm_num [dusartPrimeRow_of_explicit_18033]
      · apply DusartPrimeRowsChain.cons
        · norm_num [dusartPrimeRow_of_explicit_18033]
        · norm_num [dusartPrimeRow_of_explicit_18033]
        · apply DusartPrimeRowsChain.cons
          · norm_num [dusartPrimeRow_of_explicit_18033]
          · norm_num [dusartPrimeRow_of_explicit_18033]
          · apply DusartPrimeRowsChain.cons
            · norm_num [dusartPrimeRow_of_explicit_18033]
            · norm_num [dusartPrimeRow_of_explicit_18033]
            · apply DusartPrimeRowsChain.cons
              · norm_num [dusartPrimeRow_of_explicit_18033]
              · norm_num [dusartPrimeRow_of_explicit_18033]
              · apply DusartPrimeRowsChain.cons
                · norm_num [dusartPrimeRow_of_explicit_18033]
                · norm_num [dusartPrimeRow_of_explicit_18033]
                · apply DusartPrimeRowsChain.empty
                  norm_num [dusartPrimeRow_of_explicit_18033, dusartPrimeRow_of_explicit_right]

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_17159_18040_part09 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_18033 (p := 17783) (q := 17789) (by exact lowPrime_17789) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18033 (p := 17789) (q := 17791) (by exact lowPrime_17791) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18033 (p := 17791) (q := 17807) (by exact lowPrime_17807) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18033 (p := 17807) (q := 17827) (by exact lowPrime_17827) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18033 (p := 17827) (q := 17837) (by exact lowPrime_17837) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18033 (p := 17837) (q := 17839) (by exact lowPrime_17839) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18033 (p := 17839) (q := 17851) (by exact lowPrime_17851) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18033 (p := 17851) (q := 17863) (by exact lowPrime_17863) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_17159_18040_part09_chain :
    DusartPrimeRowsChain 17783 17862 dusartPrimeRows_17159_18040_part09 := by
  apply DusartPrimeRowsChain.cons
  · norm_num [dusartPrimeRow_of_explicit_18033]
  · norm_num [dusartPrimeRow_of_explicit_18033]
  · apply DusartPrimeRowsChain.cons
    · norm_num [dusartPrimeRow_of_explicit_18033]
    · norm_num [dusartPrimeRow_of_explicit_18033]
    · apply DusartPrimeRowsChain.cons
      · norm_num [dusartPrimeRow_of_explicit_18033]
      · norm_num [dusartPrimeRow_of_explicit_18033]
      · apply DusartPrimeRowsChain.cons
        · norm_num [dusartPrimeRow_of_explicit_18033]
        · norm_num [dusartPrimeRow_of_explicit_18033]
        · apply DusartPrimeRowsChain.cons
          · norm_num [dusartPrimeRow_of_explicit_18033]
          · norm_num [dusartPrimeRow_of_explicit_18033]
          · apply DusartPrimeRowsChain.cons
            · norm_num [dusartPrimeRow_of_explicit_18033]
            · norm_num [dusartPrimeRow_of_explicit_18033]
            · apply DusartPrimeRowsChain.cons
              · norm_num [dusartPrimeRow_of_explicit_18033]
              · norm_num [dusartPrimeRow_of_explicit_18033]
              · apply DusartPrimeRowsChain.cons
                · norm_num [dusartPrimeRow_of_explicit_18033]
                · norm_num [dusartPrimeRow_of_explicit_18033]
                · apply DusartPrimeRowsChain.empty
                  norm_num [dusartPrimeRow_of_explicit_18033, dusartPrimeRow_of_explicit_right]

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_17159_18040_part10 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_18033 (p := 17863) (q := 17881) (by exact lowPrime_17881) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18033 (p := 17881) (q := 17891) (by exact lowPrime_17891) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18033 (p := 17891) (q := 17903) (by exact lowPrime_17903) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18033 (p := 17903) (q := 17909) (by exact lowPrime_17909) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18033 (p := 17909) (q := 17911) (by exact lowPrime_17911) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18033 (p := 17911) (q := 17921) (by exact lowPrime_17921) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18033 (p := 17921) (q := 17923) (by exact lowPrime_17923) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18033 (p := 17923) (q := 17929) (by exact lowPrime_17929) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_17159_18040_part10_chain :
    DusartPrimeRowsChain 17863 17928 dusartPrimeRows_17159_18040_part10 := by
  apply DusartPrimeRowsChain.cons
  · norm_num [dusartPrimeRow_of_explicit_18033]
  · norm_num [dusartPrimeRow_of_explicit_18033]
  · apply DusartPrimeRowsChain.cons
    · norm_num [dusartPrimeRow_of_explicit_18033]
    · norm_num [dusartPrimeRow_of_explicit_18033]
    · apply DusartPrimeRowsChain.cons
      · norm_num [dusartPrimeRow_of_explicit_18033]
      · norm_num [dusartPrimeRow_of_explicit_18033]
      · apply DusartPrimeRowsChain.cons
        · norm_num [dusartPrimeRow_of_explicit_18033]
        · norm_num [dusartPrimeRow_of_explicit_18033]
        · apply DusartPrimeRowsChain.cons
          · norm_num [dusartPrimeRow_of_explicit_18033]
          · norm_num [dusartPrimeRow_of_explicit_18033]
          · apply DusartPrimeRowsChain.cons
            · norm_num [dusartPrimeRow_of_explicit_18033]
            · norm_num [dusartPrimeRow_of_explicit_18033]
            · apply DusartPrimeRowsChain.cons
              · norm_num [dusartPrimeRow_of_explicit_18033]
              · norm_num [dusartPrimeRow_of_explicit_18033]
              · apply DusartPrimeRowsChain.cons
                · norm_num [dusartPrimeRow_of_explicit_18033]
                · norm_num [dusartPrimeRow_of_explicit_18033]
                · apply DusartPrimeRowsChain.empty
                  norm_num [dusartPrimeRow_of_explicit_18033, dusartPrimeRow_of_explicit_right]
