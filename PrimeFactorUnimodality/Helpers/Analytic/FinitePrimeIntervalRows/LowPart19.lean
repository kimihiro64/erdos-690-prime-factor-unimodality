import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowBase

set_option autoImplicit false
set_option maxRecDepth 1000000

/-! # Lower finite Dusart prefix chunk 19 -/

namespace PrimeFactorUnimodality

noncomputable section
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_19949 : Nat.Prime 19949 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 19949 19948 1 2 [2, 2, 4987]
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
    · apply IsUnit.of_mul_eq_one (9974 : ZMod 19949)
      decide
    · apply IsUnit.of_mul_eq_one (1330 : ZMod 19949)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_19961 : Nat.Prime 19961 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 19961 19960 1 6 [2, 2, 2, 5, 499]
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
    · apply IsUnit.of_mul_eq_one (9980 : ZMod 19961)
      decide
    · apply IsUnit.of_mul_eq_one (18593 : ZMod 19961)
      decide
    · apply IsUnit.of_mul_eq_one (12847 : ZMod 19961)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_19963 : Nat.Prime 19963 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 19963 19962 1 2 [2, 3, 3, 1109]
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
    · apply IsUnit.of_mul_eq_one (9981 : ZMod 19963)
      decide
    · apply IsUnit.of_mul_eq_one (11193 : ZMod 19963)
      decide
    · apply IsUnit.of_mul_eq_one (19575 : ZMod 19963)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_19973 : Nat.Prime 19973 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 19973 19972 1 2 [2, 2, 4993]
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
    · apply IsUnit.of_mul_eq_one (9986 : ZMod 19973)
      decide
    · apply IsUnit.of_mul_eq_one (17310 : ZMod 19973)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_19979 : Nat.Prime 19979 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 19979 19978 1 2 [2, 7, 1427]
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
    · apply IsUnit.of_mul_eq_one (9989 : ZMod 19979)
      decide
    · apply IsUnit.of_mul_eq_one (7432 : ZMod 19979)
      decide
    · apply IsUnit.of_mul_eq_one (16351 : ZMod 19979)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_19991 : Nat.Prime 19991 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 19991 19990 1 11 [2, 5, 1999]
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
    · apply IsUnit.of_mul_eq_one (9995 : ZMod 19991)
      decide
    · apply IsUnit.of_mul_eq_one (10094 : ZMod 19991)
      decide
    · apply IsUnit.of_mul_eq_one (401 : ZMod 19991)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_19993 : Nat.Prime 19993 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 19993 19992 1 10 [2, 2, 2, 3, 7, 7, 17]
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
    · apply IsUnit.of_mul_eq_one (9996 : ZMod 19993)
      decide
    · apply IsUnit.of_mul_eq_one (15315 : ZMod 19993)
      decide
    · apply IsUnit.of_mul_eq_one (3406 : ZMod 19993)
      decide
    · apply IsUnit.of_mul_eq_one (3057 : ZMod 19993)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_19997 : Nat.Prime 19997 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 19997 19996 1 2 [2, 2, 4999]
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
    · apply IsUnit.of_mul_eq_one (9998 : ZMod 19997)
      decide
    · apply IsUnit.of_mul_eq_one (9332 : ZMod 19997)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_21187 : Nat.Prime 21187 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 21187 21186 1 2 [2, 3, 3, 11, 107]
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
    · apply IsUnit.of_mul_eq_one (10593 : ZMod 21187)
      decide
    · apply IsUnit.of_mul_eq_one (15814 : ZMod 21187)
      decide
    · apply IsUnit.of_mul_eq_one (14840 : ZMod 21187)
      decide
    · apply IsUnit.of_mul_eq_one (12367 : ZMod 21187)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_21191 : Nat.Prime 21191 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 21191 21190 1 7 [2, 5, 13, 163]
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
    · apply IsUnit.of_mul_eq_one (10595 : ZMod 21191)
      decide
    · apply IsUnit.of_mul_eq_one (15486 : ZMod 21191)
      decide
    · apply IsUnit.of_mul_eq_one (20064 : ZMod 21191)
      decide
    · apply IsUnit.of_mul_eq_one (19743 : ZMod 21191)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_21193 : Nat.Prime 21193 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 21193 21192 1 11 [2, 2, 2, 3, 883]
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
    · apply IsUnit.of_mul_eq_one (10596 : ZMod 21193)
      decide
    · apply IsUnit.of_mul_eq_one (6349 : ZMod 21193)
      decide
    · apply IsUnit.of_mul_eq_one (12932 : ZMod 21193)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_21211 : Nat.Prime 21211 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 21211 21210 1 2 [2, 3, 5, 7, 101]
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
    · apply IsUnit.of_mul_eq_one (10605 : ZMod 21211)
      decide
    · apply IsUnit.of_mul_eq_one (9761 : ZMod 21211)
      decide
    · apply IsUnit.of_mul_eq_one (6205 : ZMod 21211)
      decide
    · apply IsUnit.of_mul_eq_one (391 : ZMod 21211)
      decide
    · apply IsUnit.of_mul_eq_one (19429 : ZMod 21211)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_21221 : Nat.Prime 21221 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 21221 21220 1 2 [2, 2, 5, 1061]
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
    · apply IsUnit.of_mul_eq_one (10610 : ZMod 21221)
      decide
    · apply IsUnit.of_mul_eq_one (2914 : ZMod 21221)
      decide
    · apply IsUnit.of_mul_eq_one (15405 : ZMod 21221)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_21227 : Nat.Prime 21227 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 21227 21226 1 2 [2, 10613]
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
    · apply IsUnit.of_mul_eq_one (10613 : ZMod 21227)
      decide
    · apply IsUnit.of_mul_eq_one (7076 : ZMod 21227)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_21247 : Nat.Prime 21247 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 21247 21246 1 3 [2, 3, 3541]
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
    · apply IsUnit.of_mul_eq_one (10623 : ZMod 21247)
      decide
    · apply IsUnit.of_mul_eq_one (10249 : ZMod 21247)
      decide
    · apply IsUnit.of_mul_eq_one (16840 : ZMod 21247)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_21269 : Nat.Prime 21269 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 21269 21268 1 2 [2, 2, 13, 409]
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
    · apply IsUnit.of_mul_eq_one (10634 : ZMod 21269)
      decide
    · apply IsUnit.of_mul_eq_one (1668 : ZMod 21269)
      decide
    · apply IsUnit.of_mul_eq_one (7840 : ZMod 21269)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_21277 : Nat.Prime 21277 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 21277 21276 1 6 [2, 2, 3, 3, 3, 197]
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
    · apply IsUnit.of_mul_eq_one (10638 : ZMod 21277)
      decide
    · apply IsUnit.of_mul_eq_one (11411 : ZMod 21277)
      decide
    · apply IsUnit.of_mul_eq_one (17493 : ZMod 21277)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_21283 : Nat.Prime 21283 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 21283 21282 1 11 [2, 3, 3547]
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
    · apply IsUnit.of_mul_eq_one (10641 : ZMod 21283)
      decide
    · apply IsUnit.of_mul_eq_one (17823 : ZMod 21283)
      decide
    · apply IsUnit.of_mul_eq_one (19323 : ZMod 21283)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_21313 : Nat.Prime 21313 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 21313 21312 1 5 [2, 2, 2, 2, 2, 2, 3, 3, 37]
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
    · apply IsUnit.of_mul_eq_one (10656 : ZMod 21313)
      decide
    · apply IsUnit.of_mul_eq_one (16040 : ZMod 21313)
      decide
    · apply IsUnit.of_mul_eq_one (8113 : ZMod 21313)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_21317 : Nat.Prime 21317 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 21317 21316 1 2 [2, 2, 73, 73]
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
    · apply IsUnit.of_mul_eq_one (10658 : ZMod 21317)
      decide
    · apply IsUnit.of_mul_eq_one (4052 : ZMod 21317)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_21319 : Nat.Prime 21319 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 21319 21318 1 14 [2, 3, 11, 17, 19]
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
    · apply IsUnit.of_mul_eq_one (10659 : ZMod 21319)
      decide
    · apply IsUnit.of_mul_eq_one (17741 : ZMod 21319)
      decide
    · apply IsUnit.of_mul_eq_one (428 : ZMod 21319)
      decide
    · apply IsUnit.of_mul_eq_one (13796 : ZMod 21319)
      decide
    · apply IsUnit.of_mul_eq_one (14593 : ZMod 21319)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_21323 : Nat.Prime 21323 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 21323 21322 1 5 [2, 7, 1523]
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
    · apply IsUnit.of_mul_eq_one (10661 : ZMod 21323)
      decide
    · apply IsUnit.of_mul_eq_one (12616 : ZMod 21323)
      decide
    · apply IsUnit.of_mul_eq_one (7854 : ZMod 21323)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_21341 : Nat.Prime 21341 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 21341 21340 1 2 [2, 2, 5, 11, 97]
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
    · apply IsUnit.of_mul_eq_one (10670 : ZMod 21341)
      decide
    · apply IsUnit.of_mul_eq_one (177 : ZMod 21341)
      decide
    · apply IsUnit.of_mul_eq_one (7465 : ZMod 21341)
      decide
    · apply IsUnit.of_mul_eq_one (8649 : ZMod 21341)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_21347 : Nat.Prime 21347 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 21347 21346 1 2 [2, 13, 821]
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
    · apply IsUnit.of_mul_eq_one (10673 : ZMod 21347)
      decide
    · apply IsUnit.of_mul_eq_one (747 : ZMod 21347)
      decide
    · apply IsUnit.of_mul_eq_one (10413 : ZMod 21347)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_21377 : Nat.Prime 21377 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 21377 21376 1 3 [2, 2, 2, 2, 2, 2, 2, 167]
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
    · apply IsUnit.of_mul_eq_one (10688 : ZMod 21377)
      decide
    · apply IsUnit.of_mul_eq_one (17256 : ZMod 21377)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_21379 : Nat.Prime 21379 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 21379 21378 1 2 [2, 3, 7, 509]
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
    · apply IsUnit.of_mul_eq_one (10689 : ZMod 21379)
      decide
    · apply IsUnit.of_mul_eq_one (19885 : ZMod 21379)
      decide
    · apply IsUnit.of_mul_eq_one (13349 : ZMod 21379)
      decide
    · apply IsUnit.of_mul_eq_one (1728 : ZMod 21379)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_21383 : Nat.Prime 21383 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 21383 21382 1 5 [2, 10691]
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
    · apply IsUnit.of_mul_eq_one (10691 : ZMod 21383)
      decide
    · apply IsUnit.of_mul_eq_one (891 : ZMod 21383)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_21391 : Nat.Prime 21391 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 21391 21390 1 6 [2, 3, 5, 23, 31]
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
    · apply IsUnit.of_mul_eq_one (10695 : ZMod 21391)
      decide
    · apply IsUnit.of_mul_eq_one (7838 : ZMod 21391)
      decide
    · apply IsUnit.of_mul_eq_one (7379 : ZMod 21391)
      decide
    · apply IsUnit.of_mul_eq_one (15527 : ZMod 21391)
      decide
    · apply IsUnit.of_mul_eq_one (18913 : ZMod 21391)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_21397 : Nat.Prime 21397 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 21397 21396 1 2 [2, 2, 3, 1783]
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
    · apply IsUnit.of_mul_eq_one (10698 : ZMod 21397)
      decide
    · apply IsUnit.of_mul_eq_one (21092 : ZMod 21397)
      decide
    · apply IsUnit.of_mul_eq_one (18821 : ZMod 21397)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_21401 : Nat.Prime 21401 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 21401 21400 1 3 [2, 2, 2, 5, 5, 107]
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
    · apply IsUnit.of_mul_eq_one (10700 : ZMod 21401)
      decide
    · apply IsUnit.of_mul_eq_one (19026 : ZMod 21401)
      decide
    · apply IsUnit.of_mul_eq_one (8897 : ZMod 21401)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_21407 : Nat.Prime 21407 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 21407 21406 1 5 [2, 7, 11, 139]
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
    · apply IsUnit.of_mul_eq_one (10703 : ZMod 21407)
      decide
    · apply IsUnit.of_mul_eq_one (20311 : ZMod 21407)
      decide
    · apply IsUnit.of_mul_eq_one (4887 : ZMod 21407)
      decide
    · apply IsUnit.of_mul_eq_one (20612 : ZMod 21407)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_21419 : Nat.Prime 21419 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 21419 21418 1 2 [2, 10709]
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
    · apply IsUnit.of_mul_eq_one (10709 : ZMod 21419)
      decide
    · apply IsUnit.of_mul_eq_one (7140 : ZMod 21419)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_21433 : Nat.Prime 21433 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 21433 21432 1 5 [2, 2, 2, 3, 19, 47]
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
    · apply IsUnit.of_mul_eq_one (10716 : ZMod 21433)
      decide
    · apply IsUnit.of_mul_eq_one (9173 : ZMod 21433)
      decide
    · apply IsUnit.of_mul_eq_one (14244 : ZMod 21433)
      decide
    · apply IsUnit.of_mul_eq_one (19404 : ZMod 21433)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_21467 : Nat.Prime 21467 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 21467 21466 1 2 [2, 10733]
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
    · apply IsUnit.of_mul_eq_one (10733 : ZMod 21467)
      decide
    · apply IsUnit.of_mul_eq_one (7156 : ZMod 21467)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_21481 : Nat.Prime 21481 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 21481 21480 1 13 [2, 2, 2, 3, 5, 179]
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
    · apply IsUnit.of_mul_eq_one (10740 : ZMod 21481)
      decide
    · apply IsUnit.of_mul_eq_one (5718 : ZMod 21481)
      decide
    · apply IsUnit.of_mul_eq_one (21406 : ZMod 21481)
      decide
    · apply IsUnit.of_mul_eq_one (17671 : ZMod 21481)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_21487 : Nat.Prime 21487 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 21487 21486 1 3 [2, 3, 3581]
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
    · apply IsUnit.of_mul_eq_one (10743 : ZMod 21487)
      decide
    · apply IsUnit.of_mul_eq_one (11424 : ZMod 21487)
      decide
    · apply IsUnit.of_mul_eq_one (974 : ZMod 21487)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_21491 : Nat.Prime 21491 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 21491 21490 1 2 [2, 5, 7, 307]
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
    · apply IsUnit.of_mul_eq_one (10745 : ZMod 21491)
      decide
    · apply IsUnit.of_mul_eq_one (17394 : ZMod 21491)
      decide
    · apply IsUnit.of_mul_eq_one (2984 : ZMod 21491)
      decide
    · apply IsUnit.of_mul_eq_one (10695 : ZMod 21491)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_21493 : Nat.Prime 21493 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 21493 21492 1 2 [2, 2, 3, 3, 3, 199]
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
    · apply IsUnit.of_mul_eq_one (10746 : ZMod 21493)
      decide
    · apply IsUnit.of_mul_eq_one (6316 : ZMod 21493)
      decide
    · apply IsUnit.of_mul_eq_one (19339 : ZMod 21493)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_21499 : Nat.Prime 21499 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 21499 21498 1 3 [2, 3, 3583]
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
    · apply IsUnit.of_mul_eq_one (10749 : ZMod 21499)
      decide
    · apply IsUnit.of_mul_eq_one (2054 : ZMod 21499)
      decide
    · apply IsUnit.of_mul_eq_one (7944 : ZMod 21499)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_21503 : Nat.Prime 21503 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 21503 21502 1 5 [2, 13, 827]
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
    · apply IsUnit.of_mul_eq_one (10751 : ZMod 21503)
      decide
    · apply IsUnit.of_mul_eq_one (15718 : ZMod 21503)
      decide
    · apply IsUnit.of_mul_eq_one (15910 : ZMod 21503)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_21517 : Nat.Prime 21517 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 21517 21516 1 5 [2, 2, 3, 11, 163]
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
    · apply IsUnit.of_mul_eq_one (10758 : ZMod 21517)
      decide
    · apply IsUnit.of_mul_eq_one (13614 : ZMod 21517)
      decide
    · apply IsUnit.of_mul_eq_one (11203 : ZMod 21517)
      decide
    · apply IsUnit.of_mul_eq_one (11816 : ZMod 21517)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_21521 : Nat.Prime 21521 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 21521 21520 1 3 [2, 2, 2, 2, 5, 269]
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
    · apply IsUnit.of_mul_eq_one (10760 : ZMod 21521)
      decide
    · apply IsUnit.of_mul_eq_one (9195 : ZMod 21521)
      decide
    · apply IsUnit.of_mul_eq_one (12060 : ZMod 21521)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_21523 : Nat.Prime 21523 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 21523 21522 1 2 [2, 3, 17, 211]
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
    · apply IsUnit.of_mul_eq_one (10761 : ZMod 21523)
      decide
    · apply IsUnit.of_mul_eq_one (10357 : ZMod 21523)
      decide
    · apply IsUnit.of_mul_eq_one (10195 : ZMod 21523)
      decide
    · apply IsUnit.of_mul_eq_one (1610 : ZMod 21523)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_21529 : Nat.Prime 21529 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 21529 21528 1 11 [2, 2, 2, 3, 3, 13, 23]
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
    · apply IsUnit.of_mul_eq_one (10764 : ZMod 21529)
      decide
    · apply IsUnit.of_mul_eq_one (13028 : ZMod 21529)
      decide
    · apply IsUnit.of_mul_eq_one (20321 : ZMod 21529)
      decide
    · apply IsUnit.of_mul_eq_one (4011 : ZMod 21529)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_21557 : Nat.Prime 21557 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 21557 21556 1 2 [2, 2, 17, 317]
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
    · apply IsUnit.of_mul_eq_one (10778 : ZMod 21557)
      decide
    · apply IsUnit.of_mul_eq_one (18082 : ZMod 21557)
      decide
    · apply IsUnit.of_mul_eq_one (16310 : ZMod 21557)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_21559 : Nat.Prime 21559 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 21559 21558 1 15 [2, 3, 3593]
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
    · apply IsUnit.of_mul_eq_one (10779 : ZMod 21559)
      decide
    · apply IsUnit.of_mul_eq_one (1993 : ZMod 21559)
      decide
    · apply IsUnit.of_mul_eq_one (20754 : ZMod 21559)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_21563 : Nat.Prime 21563 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 21563 21562 1 2 [2, 10781]
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
    · apply IsUnit.of_mul_eq_one (10781 : ZMod 21563)
      decide
    · apply IsUnit.of_mul_eq_one (7188 : ZMod 21563)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_21569 : Nat.Prime 21569 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 21569 21568 1 3 [2, 2, 2, 2, 2, 2, 337]
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
    · apply IsUnit.of_mul_eq_one (10784 : ZMod 21569)
      decide
    · apply IsUnit.of_mul_eq_one (15354 : ZMod 21569)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_21577 : Nat.Prime 21577 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 21577 21576 1 5 [2, 2, 2, 3, 29, 31]
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
    · apply IsUnit.of_mul_eq_one (10788 : ZMod 21577)
      decide
    · apply IsUnit.of_mul_eq_one (12086 : ZMod 21577)
      decide
    · apply IsUnit.of_mul_eq_one (5426 : ZMod 21577)
      decide
    · apply IsUnit.of_mul_eq_one (10815 : ZMod 21577)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_21587 : Nat.Prime 21587 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 21587 21586 1 2 [2, 43, 251]
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
    · apply IsUnit.of_mul_eq_one (10793 : ZMod 21587)
      decide
    · apply IsUnit.of_mul_eq_one (14498 : ZMod 21587)
      decide
    · apply IsUnit.of_mul_eq_one (19534 : ZMod 21587)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_21589 : Nat.Prime 21589 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 21589 21588 1 2 [2, 2, 3, 7, 257]
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
    · apply IsUnit.of_mul_eq_one (10794 : ZMod 21589)
      decide
    · apply IsUnit.of_mul_eq_one (19378 : ZMod 21589)
      decide
    · apply IsUnit.of_mul_eq_one (9916 : ZMod 21589)
      decide
    · apply IsUnit.of_mul_eq_one (628 : ZMod 21589)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_21599 : Nat.Prime 21599 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 21599 21598 1 7 [2, 10799]
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
    · apply IsUnit.of_mul_eq_one (10799 : ZMod 21599)
      decide
    · apply IsUnit.of_mul_eq_one (450 : ZMod 21599)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_21601 : Nat.Prime 21601 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 21601 21600 1 7 [2, 2, 2, 2, 2, 3, 3, 3, 5, 5]
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
    · apply IsUnit.of_mul_eq_one (10800 : ZMod 21601)
      decide
    · apply IsUnit.of_mul_eq_one (13005 : ZMod 21601)
      decide
    · apply IsUnit.of_mul_eq_one (11701 : ZMod 21601)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_21611 : Nat.Prime 21611 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 21611 21610 1 2 [2, 5, 2161]
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
    · apply IsUnit.of_mul_eq_one (10805 : ZMod 21611)
      decide
    · apply IsUnit.of_mul_eq_one (15909 : ZMod 21611)
      decide
    · apply IsUnit.of_mul_eq_one (21442 : ZMod 21611)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_21613 : Nat.Prime 21613 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 21613 21612 1 2 [2, 2, 3, 1801]
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
    · apply IsUnit.of_mul_eq_one (10806 : ZMod 21613)
      decide
    · apply IsUnit.of_mul_eq_one (7974 : ZMod 21613)
      decide
    · apply IsUnit.of_mul_eq_one (19201 : ZMod 21613)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_21617 : Nat.Prime 21617 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 21617 21616 1 3 [2, 2, 2, 2, 7, 193]
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
    · apply IsUnit.of_mul_eq_one (10808 : ZMod 21617)
      decide
    · apply IsUnit.of_mul_eq_one (3158 : ZMod 21617)
      decide
    · apply IsUnit.of_mul_eq_one (13459 : ZMod 21617)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
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
  · decide
  · intro q hq
    simp at hq
    rcases hq with rfl | rfl | rfl
    · apply IsUnit.of_mul_eq_one (10823 : ZMod 21647)
      decide
    · apply IsUnit.of_mul_eq_one (9293 : ZMod 21647)
      decide
    · apply IsUnit.of_mul_eq_one (15464 : ZMod 21647)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
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
  · decide
  · intro q hq
    simp at hq
    rcases hq with rfl | rfl | rfl | rfl
    · apply IsUnit.of_mul_eq_one (10824 : ZMod 21649)
      decide
    · apply IsUnit.of_mul_eq_one (2346 : ZMod 21649)
      decide
    · apply IsUnit.of_mul_eq_one (20718 : ZMod 21649)
      decide
    · apply IsUnit.of_mul_eq_one (9133 : ZMod 21649)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
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
  · decide
  · intro q hq
    simp at hq
    rcases hq with rfl | rfl | rfl | rfl
    · apply IsUnit.of_mul_eq_one (10830 : ZMod 21661)
      decide
    · apply IsUnit.of_mul_eq_one (19567 : ZMod 21661)
      decide
    · apply IsUnit.of_mul_eq_one (21184 : ZMod 21661)
      decide
    · apply IsUnit.of_mul_eq_one (21572 : ZMod 21661)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
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
  · decide
  · intro q hq
    simp at hq
    rcases hq with rfl | rfl | rfl | rfl
    · apply IsUnit.of_mul_eq_one (10836 : ZMod 21673)
      decide
    · apply IsUnit.of_mul_eq_one (7094 : ZMod 21673)
      decide
    · apply IsUnit.of_mul_eq_one (12047 : ZMod 21673)
      decide
    · apply IsUnit.of_mul_eq_one (14017 : ZMod 21673)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
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
  · decide
  · intro q hq
    simp at hq
    rcases hq with rfl | rfl | rfl
    · apply IsUnit.of_mul_eq_one (10841 : ZMod 21683)
      decide
    · apply IsUnit.of_mul_eq_one (20284 : ZMod 21683)
      decide
    · apply IsUnit.of_mul_eq_one (14982 : ZMod 21683)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
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
  · decide
  · intro q hq
    simp at hq
    rcases hq with rfl | rfl | rfl | rfl
    · apply IsUnit.of_mul_eq_one (10850 : ZMod 21701)
      decide
    · apply IsUnit.of_mul_eq_one (15281 : ZMod 21701)
      decide
    · apply IsUnit.of_mul_eq_one (10822 : ZMod 21701)
      decide
    · apply IsUnit.of_mul_eq_one (15946 : ZMod 21701)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
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
  · decide
  · intro q hq
    simp at hq
    rcases hq with rfl | rfl | rfl
    · apply IsUnit.of_mul_eq_one (10856 : ZMod 21713)
      decide
    · apply IsUnit.of_mul_eq_one (6167 : ZMod 21713)
      decide
    · apply IsUnit.of_mul_eq_one (3827 : ZMod 21713)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
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
  · decide
  · intro q hq
    simp at hq
    rcases hq with rfl | rfl | rfl | rfl
    · apply IsUnit.of_mul_eq_one (10863 : ZMod 21727)
      decide
    · apply IsUnit.of_mul_eq_one (2485 : ZMod 21727)
      decide
    · apply IsUnit.of_mul_eq_one (18663 : ZMod 21727)
      decide
    · apply IsUnit.of_mul_eq_one (19845 : ZMod 21727)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_21737 : Nat.Prime 21737 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 21737 21736 1 6 [2, 2, 2, 11, 13, 19]
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
    · apply IsUnit.of_mul_eq_one (10868 : ZMod 21737)
      decide
    · apply IsUnit.of_mul_eq_one (7760 : ZMod 21737)
      decide
    · apply IsUnit.of_mul_eq_one (13561 : ZMod 21737)
      decide
    · apply IsUnit.of_mul_eq_one (5733 : ZMod 21737)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_21739 : Nat.Prime 21739 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 21739 21738 1 2 [2, 3, 3623]
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
    · apply IsUnit.of_mul_eq_one (10869 : ZMod 21739)
      decide
    · apply IsUnit.of_mul_eq_one (12233 : ZMod 21739)
      decide
    · apply IsUnit.of_mul_eq_one (16218 : ZMod 21739)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_21751 : Nat.Prime 21751 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 21751 21750 1 3 [2, 3, 5, 5, 5, 29]
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
    · apply IsUnit.of_mul_eq_one (10875 : ZMod 21751)
      decide
    · apply IsUnit.of_mul_eq_one (19070 : ZMod 21751)
      decide
    · apply IsUnit.of_mul_eq_one (18854 : ZMod 21751)
      decide
    · apply IsUnit.of_mul_eq_one (20340 : ZMod 21751)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_21757 : Nat.Prime 21757 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 21757 21756 1 5 [2, 2, 3, 7, 7, 37]
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
    · apply IsUnit.of_mul_eq_one (10878 : ZMod 21757)
      decide
    · apply IsUnit.of_mul_eq_one (14455 : ZMod 21757)
      decide
    · apply IsUnit.of_mul_eq_one (11136 : ZMod 21757)
      decide
    · apply IsUnit.of_mul_eq_one (10797 : ZMod 21757)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_21767 : Nat.Prime 21767 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 21767 21766 1 5 [2, 10883]
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
    · apply IsUnit.of_mul_eq_one (10883 : ZMod 21767)
      decide
    · apply IsUnit.of_mul_eq_one (907 : ZMod 21767)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_21773 : Nat.Prime 21773 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 21773 21772 1 2 [2, 2, 5443]
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
    · apply IsUnit.of_mul_eq_one (10886 : ZMod 21773)
      decide
    · apply IsUnit.of_mul_eq_one (18870 : ZMod 21773)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_21787 : Nat.Prime 21787 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 21787 21786 1 23 [2, 3, 3631]
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
    · apply IsUnit.of_mul_eq_one (10893 : ZMod 21787)
      decide
    · apply IsUnit.of_mul_eq_one (20308 : ZMod 21787)
      decide
    · apply IsUnit.of_mul_eq_one (823 : ZMod 21787)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_21799 : Nat.Prime 21799 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 21799 21798 1 7 [2, 3, 3, 7, 173]
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
    · apply IsUnit.of_mul_eq_one (10899 : ZMod 21799)
      decide
    · apply IsUnit.of_mul_eq_one (1659 : ZMod 21799)
      decide
    · apply IsUnit.of_mul_eq_one (12191 : ZMod 21799)
      decide
    · apply IsUnit.of_mul_eq_one (15652 : ZMod 21799)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_21803 : Nat.Prime 21803 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 21803 21802 1 2 [2, 11, 991]
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
    · apply IsUnit.of_mul_eq_one (10901 : ZMod 21803)
      decide
    · apply IsUnit.of_mul_eq_one (5777 : ZMod 21803)
      decide
    · apply IsUnit.of_mul_eq_one (10208 : ZMod 21803)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_21817 : Nat.Prime 21817 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 21817 21816 1 7 [2, 2, 2, 3, 3, 3, 101]
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
    · apply IsUnit.of_mul_eq_one (10908 : ZMod 21817)
      decide
    · apply IsUnit.of_mul_eq_one (21003 : ZMod 21817)
      decide
    · apply IsUnit.of_mul_eq_one (2906 : ZMod 21817)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_21821 : Nat.Prime 21821 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 21821 21820 1 2 [2, 2, 5, 1091]
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
    · apply IsUnit.of_mul_eq_one (10910 : ZMod 21821)
      decide
    · apply IsUnit.of_mul_eq_one (7500 : ZMod 21821)
      decide
    · apply IsUnit.of_mul_eq_one (14940 : ZMod 21821)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_21839 : Nat.Prime 21839 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 21839 21838 1 11 [2, 61, 179]
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
    · apply IsUnit.of_mul_eq_one (10919 : ZMod 21839)
      decide
    · apply IsUnit.of_mul_eq_one (7033 : ZMod 21839)
      decide
    · apply IsUnit.of_mul_eq_one (8208 : ZMod 21839)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_21841 : Nat.Prime 21841 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 21841 21840 1 11 [2, 2, 2, 2, 3, 5, 7, 13]
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
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · apply IsUnit.of_mul_eq_one (10920 : ZMod 21841)
      decide
    · apply IsUnit.of_mul_eq_one (11717 : ZMod 21841)
      decide
    · apply IsUnit.of_mul_eq_one (7116 : ZMod 21841)
      decide
    · apply IsUnit.of_mul_eq_one (6835 : ZMod 21841)
      decide
    · apply IsUnit.of_mul_eq_one (5776 : ZMod 21841)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_21851 : Nat.Prime 21851 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 21851 21850 1 6 [2, 5, 5, 19, 23]
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
    · apply IsUnit.of_mul_eq_one (10925 : ZMod 21851)
      decide
    · apply IsUnit.of_mul_eq_one (16804 : ZMod 21851)
      decide
    · apply IsUnit.of_mul_eq_one (3402 : ZMod 21851)
      decide
    · apply IsUnit.of_mul_eq_one (2445 : ZMod 21851)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_21859 : Nat.Prime 21859 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 21859 21858 1 2 [2, 3, 3643]
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
    · apply IsUnit.of_mul_eq_one (10929 : ZMod 21859)
      decide
    · apply IsUnit.of_mul_eq_one (19322 : ZMod 21859)
      decide
    · apply IsUnit.of_mul_eq_one (11103 : ZMod 21859)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_21863 : Nat.Prime 21863 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 21863 21862 1 5 [2, 17, 643]
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
    · apply IsUnit.of_mul_eq_one (10931 : ZMod 21863)
      decide
    · apply IsUnit.of_mul_eq_one (8620 : ZMod 21863)
      decide
    · apply IsUnit.of_mul_eq_one (4355 : ZMod 21863)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_21871 : Nat.Prime 21871 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 21871 21870 1 6 [2, 3, 3, 3, 3, 3, 3, 3, 5]
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
    · apply IsUnit.of_mul_eq_one (10935 : ZMod 21871)
      decide
    · apply IsUnit.of_mul_eq_one (17968 : ZMod 21871)
      decide
    · apply IsUnit.of_mul_eq_one (12548 : ZMod 21871)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_21881 : Nat.Prime 21881 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 21881 21880 1 3 [2, 2, 2, 5, 547]
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
    · apply IsUnit.of_mul_eq_one (10940 : ZMod 21881)
      decide
    · apply IsUnit.of_mul_eq_one (387 : ZMod 21881)
      decide
    · apply IsUnit.of_mul_eq_one (598 : ZMod 21881)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_21893 : Nat.Prime 21893 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 21893 21892 1 2 [2, 2, 13, 421]
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
    · apply IsUnit.of_mul_eq_one (10946 : ZMod 21893)
      decide
    · apply IsUnit.of_mul_eq_one (9950 : ZMod 21893)
      decide
    · apply IsUnit.of_mul_eq_one (17863 : ZMod 21893)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_21911 : Nat.Prime 21911 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 21911 21910 1 13 [2, 5, 7, 313]
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
    · apply IsUnit.of_mul_eq_one (10955 : ZMod 21911)
      decide
    · apply IsUnit.of_mul_eq_one (2413 : ZMod 21911)
      decide
    · apply IsUnit.of_mul_eq_one (6172 : ZMod 21911)
      decide
    · apply IsUnit.of_mul_eq_one (5511 : ZMod 21911)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_21929 : Nat.Prime 21929 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 21929 21928 1 3 [2, 2, 2, 2741]
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
    · apply IsUnit.of_mul_eq_one (10964 : ZMod 21929)
      decide
    · apply IsUnit.of_mul_eq_one (8795 : ZMod 21929)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_21937 : Nat.Prime 21937 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 21937 21936 1 7 [2, 2, 2, 2, 3, 457]
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
    · apply IsUnit.of_mul_eq_one (10968 : ZMod 21937)
      decide
    · apply IsUnit.of_mul_eq_one (4404 : ZMod 21937)
      decide
    · apply IsUnit.of_mul_eq_one (20011 : ZMod 21937)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_21943 : Nat.Prime 21943 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 21943 21942 1 5 [2, 3, 3, 23, 53]
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
    · apply IsUnit.of_mul_eq_one (10971 : ZMod 21943)
      decide
    · apply IsUnit.of_mul_eq_one (3122 : ZMod 21943)
      decide
    · apply IsUnit.of_mul_eq_one (4650 : ZMod 21943)
      decide
    · apply IsUnit.of_mul_eq_one (15752 : ZMod 21943)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_21961 : Nat.Prime 21961 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 21961 21960 1 17 [2, 2, 2, 3, 3, 5, 61]
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
    · apply IsUnit.of_mul_eq_one (10980 : ZMod 21961)
      decide
    · apply IsUnit.of_mul_eq_one (9974 : ZMod 21961)
      decide
    · apply IsUnit.of_mul_eq_one (13413 : ZMod 21961)
      decide
    · apply IsUnit.of_mul_eq_one (17855 : ZMod 21961)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_21977 : Nat.Prime 21977 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 21977 21976 1 3 [2, 2, 2, 41, 67]
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
    · apply IsUnit.of_mul_eq_one (10988 : ZMod 21977)
      decide
    · apply IsUnit.of_mul_eq_one (7023 : ZMod 21977)
      decide
    · apply IsUnit.of_mul_eq_one (12528 : ZMod 21977)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_21991 : Nat.Prime 21991 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 21991 21990 1 3 [2, 3, 5, 733]
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
    · apply IsUnit.of_mul_eq_one (10995 : ZMod 21991)
      decide
    · apply IsUnit.of_mul_eq_one (10016 : ZMod 21991)
      decide
    · apply IsUnit.of_mul_eq_one (2477 : ZMod 21991)
      decide
    · apply IsUnit.of_mul_eq_one (11053 : ZMod 21991)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_21997 : Nat.Prime 21997 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 21997 21996 1 7 [2, 2, 3, 3, 13, 47]
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
    · apply IsUnit.of_mul_eq_one (10998 : ZMod 21997)
      decide
    · apply IsUnit.of_mul_eq_one (18128 : ZMod 21997)
      decide
    · apply IsUnit.of_mul_eq_one (1430 : ZMod 21997)
      decide
    · apply IsUnit.of_mul_eq_one (8780 : ZMod 21997)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_22003 : Nat.Prime 22003 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 22003 22002 1 2 [2, 3, 19, 193]
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
    · apply IsUnit.of_mul_eq_one (11001 : ZMod 22003)
      decide
    · apply IsUnit.of_mul_eq_one (15526 : ZMod 22003)
      decide
    · apply IsUnit.of_mul_eq_one (290 : ZMod 22003)
      decide
    · apply IsUnit.of_mul_eq_one (18761 : ZMod 22003)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_22013 : Nat.Prime 22013 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 22013 22012 1 2 [2, 2, 5503]
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
    · apply IsUnit.of_mul_eq_one (11006 : ZMod 22013)
      decide
    · apply IsUnit.of_mul_eq_one (19078 : ZMod 22013)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_22027 : Nat.Prime 22027 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 22027 22026 1 3 [2, 3, 3671]
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
    · apply IsUnit.of_mul_eq_one (11013 : ZMod 22027)
      decide
    · apply IsUnit.of_mul_eq_one (8885 : ZMod 22027)
      decide
    · apply IsUnit.of_mul_eq_one (3298 : ZMod 22027)
      decide
  · norm_num
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_20959_22026_part04 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_22026 (p := 21179) (q := 21187) (by exact lowPrime_21187) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_22026 (p := 21187) (q := 21191) (by exact lowPrime_21191) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_22026 (p := 21191) (q := 21193) (by exact lowPrime_21193) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_22026 (p := 21193) (q := 21211) (by exact lowPrime_21211) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_22026 (p := 21211) (q := 21221) (by exact lowPrime_21221) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_22026 (p := 21221) (q := 21227) (by exact lowPrime_21227) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_22026 (p := 21227) (q := 21247) (by exact lowPrime_21247) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_22026 (p := 21247) (q := 21269) (by exact lowPrime_21269) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_20959_22026_part04_chain :
    DusartPrimeRowsChain 21179 21268 dusartPrimeRows_20959_22026_part04 := by
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
                  norm_num [dusartPrimeRow_of_explicit_22026, dusartPrimeRow_of_explicit_right]

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_20959_22026_part05 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_22026 (p := 21269) (q := 21277) (by exact lowPrime_21277) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_22026 (p := 21277) (q := 21283) (by exact lowPrime_21283) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_22026 (p := 21283) (q := 21313) (by exact lowPrime_21313) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_22026 (p := 21313) (q := 21317) (by exact lowPrime_21317) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_22026 (p := 21317) (q := 21319) (by exact lowPrime_21319) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_22026 (p := 21319) (q := 21323) (by exact lowPrime_21323) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_22026 (p := 21323) (q := 21341) (by exact lowPrime_21341) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_22026 (p := 21341) (q := 21347) (by exact lowPrime_21347) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_20959_22026_part05_chain :
    DusartPrimeRowsChain 21269 21346 dusartPrimeRows_20959_22026_part05 := by
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
                  norm_num [dusartPrimeRow_of_explicit_22026, dusartPrimeRow_of_explicit_right]

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_20959_22026_part06 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_22026 (p := 21347) (q := 21377) (by exact lowPrime_21377) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_22026 (p := 21377) (q := 21379) (by exact lowPrime_21379) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_22026 (p := 21379) (q := 21383) (by exact lowPrime_21383) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_22026 (p := 21383) (q := 21391) (by exact lowPrime_21391) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_22026 (p := 21391) (q := 21397) (by exact lowPrime_21397) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_22026 (p := 21397) (q := 21401) (by exact lowPrime_21401) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_22026 (p := 21401) (q := 21407) (by exact lowPrime_21407) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_22026 (p := 21407) (q := 21419) (by exact lowPrime_21419) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_20959_22026_part06_chain :
    DusartPrimeRowsChain 21347 21418 dusartPrimeRows_20959_22026_part06 := by
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
                  norm_num [dusartPrimeRow_of_explicit_22026, dusartPrimeRow_of_explicit_right]

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_20959_22026_part07 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_22026 (p := 21419) (q := 21433) (by exact lowPrime_21433) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_22026 (p := 21433) (q := 21467) (by exact lowPrime_21467) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_22026 (p := 21467) (q := 21481) (by exact lowPrime_21481) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_22026 (p := 21481) (q := 21487) (by exact lowPrime_21487) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_22026 (p := 21487) (q := 21491) (by exact lowPrime_21491) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_22026 (p := 21491) (q := 21493) (by exact lowPrime_21493) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_22026 (p := 21493) (q := 21499) (by exact lowPrime_21499) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_22026 (p := 21499) (q := 21503) (by exact lowPrime_21503) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_20959_22026_part07_chain :
    DusartPrimeRowsChain 21419 21502 dusartPrimeRows_20959_22026_part07 := by
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
                  norm_num [dusartPrimeRow_of_explicit_22026, dusartPrimeRow_of_explicit_right]

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_20959_22026_part08 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_22026 (p := 21503) (q := 21517) (by exact lowPrime_21517) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_22026 (p := 21517) (q := 21521) (by exact lowPrime_21521) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_22026 (p := 21521) (q := 21523) (by exact lowPrime_21523) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_22026 (p := 21523) (q := 21529) (by exact lowPrime_21529) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_22026 (p := 21529) (q := 21557) (by exact lowPrime_21557) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_22026 (p := 21557) (q := 21559) (by exact lowPrime_21559) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_22026 (p := 21559) (q := 21563) (by exact lowPrime_21563) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_22026 (p := 21563) (q := 21569) (by exact lowPrime_21569) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_20959_22026_part08_chain :
    DusartPrimeRowsChain 21503 21568 dusartPrimeRows_20959_22026_part08 := by
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
                  norm_num [dusartPrimeRow_of_explicit_22026, dusartPrimeRow_of_explicit_right]

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_20959_22026_part09 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_22026 (p := 21569) (q := 21577) (by exact lowPrime_21577) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_22026 (p := 21577) (q := 21587) (by exact lowPrime_21587) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_22026 (p := 21587) (q := 21589) (by exact lowPrime_21589) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_22026 (p := 21589) (q := 21599) (by exact lowPrime_21599) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_22026 (p := 21599) (q := 21601) (by exact lowPrime_21601) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_22026 (p := 21601) (q := 21611) (by exact lowPrime_21611) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_22026 (p := 21611) (q := 21613) (by exact lowPrime_21613) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_22026 (p := 21613) (q := 21617) (by exact lowPrime_21617) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_20959_22026_part09_chain :
    DusartPrimeRowsChain 21569 21616 dusartPrimeRows_20959_22026_part09 := by
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
                  norm_num [dusartPrimeRow_of_explicit_22026, dusartPrimeRow_of_explicit_right]

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
    DusartPrimeRowsChain 21617 21726 dusartPrimeRows_20959_22026_part10 := by
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
                  norm_num [dusartPrimeRow_of_explicit_22026, dusartPrimeRow_of_explicit_right]

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_20959_22026_part11 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_22026 (p := 21727) (q := 21737) (by exact lowPrime_21737) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_22026 (p := 21737) (q := 21739) (by exact lowPrime_21739) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_22026 (p := 21739) (q := 21751) (by exact lowPrime_21751) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_22026 (p := 21751) (q := 21757) (by exact lowPrime_21757) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_22026 (p := 21757) (q := 21767) (by exact lowPrime_21767) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_22026 (p := 21767) (q := 21773) (by exact lowPrime_21773) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_22026 (p := 21773) (q := 21787) (by exact lowPrime_21787) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_22026 (p := 21787) (q := 21799) (by exact lowPrime_21799) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_20959_22026_part11_chain :
    DusartPrimeRowsChain 21727 21798 dusartPrimeRows_20959_22026_part11 := by
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
                  norm_num [dusartPrimeRow_of_explicit_22026, dusartPrimeRow_of_explicit_right]

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_20959_22026_part12 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_22026 (p := 21799) (q := 21803) (by exact lowPrime_21803) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_22026 (p := 21803) (q := 21817) (by exact lowPrime_21817) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_22026 (p := 21817) (q := 21821) (by exact lowPrime_21821) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_22026 (p := 21821) (q := 21839) (by exact lowPrime_21839) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_22026 (p := 21839) (q := 21841) (by exact lowPrime_21841) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_22026 (p := 21841) (q := 21851) (by exact lowPrime_21851) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_22026 (p := 21851) (q := 21859) (by exact lowPrime_21859) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_22026 (p := 21859) (q := 21863) (by exact lowPrime_21863) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_20959_22026_part12_chain :
    DusartPrimeRowsChain 21799 21862 dusartPrimeRows_20959_22026_part12 := by
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
                  norm_num [dusartPrimeRow_of_explicit_22026, dusartPrimeRow_of_explicit_right]

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_20959_22026_part13 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_22026 (p := 21863) (q := 21871) (by exact lowPrime_21871) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_22026 (p := 21871) (q := 21881) (by exact lowPrime_21881) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_22026 (p := 21881) (q := 21893) (by exact lowPrime_21893) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_22026 (p := 21893) (q := 21911) (by exact lowPrime_21911) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_22026 (p := 21911) (q := 21929) (by exact lowPrime_21929) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_22026 (p := 21929) (q := 21937) (by exact lowPrime_21937) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_22026 (p := 21937) (q := 21943) (by exact lowPrime_21943) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_22026 (p := 21943) (q := 21961) (by exact lowPrime_21961) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_20959_22026_part13_chain :
    DusartPrimeRowsChain 21863 21960 dusartPrimeRows_20959_22026_part13 := by
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
                  norm_num [dusartPrimeRow_of_explicit_22026, dusartPrimeRow_of_explicit_right]

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_20959_22026_part14 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_22026 (p := 21961) (q := 21977) (by exact lowPrime_21977) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_22026 (p := 21977) (q := 21991) (by exact lowPrime_21991) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_22026 (p := 21991) (q := 21997) (by exact lowPrime_21997) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_22026 (p := 21997) (q := 22003) (by exact lowPrime_22003) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_22026 (p := 22003) (q := 22013) (by exact lowPrime_22013) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_22026 (p := 22013) (q := 22027) (by exact lowPrime_22027) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_20959_22026_part14_chain :
    DusartPrimeRowsChain 21961 22026 dusartPrimeRows_20959_22026_part14 := by
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
            · apply DusartPrimeRowsChain.empty
              norm_num [dusartPrimeRow_of_explicit_22026, dusartPrimeRow_of_explicit_right]

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_19937_20958_part01 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_20952 (p := 19937) (q := 19949) (by exact lowPrime_19949) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_20952 (p := 19949) (q := 19961) (by exact lowPrime_19961) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_20952 (p := 19961) (q := 19963) (by exact lowPrime_19963) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_20952 (p := 19963) (q := 19973) (by exact lowPrime_19973) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_20952 (p := 19973) (q := 19979) (by exact lowPrime_19979) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_20952 (p := 19979) (q := 19991) (by exact lowPrime_19991) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_20952 (p := 19991) (q := 19993) (by exact lowPrime_19993) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_20952 (p := 19993) (q := 19997) (by exact lowPrime_19997) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_19937_20958_part01_chain :
    DusartPrimeRowsChain 19937 19996 dusartPrimeRows_19937_20958_part01 := by
  apply DusartPrimeRowsChain.cons
  · norm_num [dusartPrimeRow_of_explicit_20952]
  · norm_num [dusartPrimeRow_of_explicit_20952]
  · apply DusartPrimeRowsChain.cons
    · norm_num [dusartPrimeRow_of_explicit_20952]
    · norm_num [dusartPrimeRow_of_explicit_20952]
    · apply DusartPrimeRowsChain.cons
      · norm_num [dusartPrimeRow_of_explicit_20952]
      · norm_num [dusartPrimeRow_of_explicit_20952]
      · apply DusartPrimeRowsChain.cons
        · norm_num [dusartPrimeRow_of_explicit_20952]
        · norm_num [dusartPrimeRow_of_explicit_20952]
        · apply DusartPrimeRowsChain.cons
          · norm_num [dusartPrimeRow_of_explicit_20952]
          · norm_num [dusartPrimeRow_of_explicit_20952]
          · apply DusartPrimeRowsChain.cons
            · norm_num [dusartPrimeRow_of_explicit_20952]
            · norm_num [dusartPrimeRow_of_explicit_20952]
            · apply DusartPrimeRowsChain.cons
              · norm_num [dusartPrimeRow_of_explicit_20952]
              · norm_num [dusartPrimeRow_of_explicit_20952]
              · apply DusartPrimeRowsChain.cons
                · norm_num [dusartPrimeRow_of_explicit_20952]
                · norm_num [dusartPrimeRow_of_explicit_20952]
                · apply DusartPrimeRowsChain.empty
                  norm_num [dusartPrimeRow_of_explicit_20952, dusartPrimeRow_of_explicit_right]
