import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowBase

set_option autoImplicit false
set_option maxRecDepth 1000000

/-! # Lower finite Dusart prefix chunk 20 -/

namespace PrimeFactorUnimodality

noncomputable section
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_20011 : Nat.Prime 20011 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 20011 20010 1 12 [2, 3, 5, 23, 29]
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
    · apply IsUnit.of_mul_eq_one (10005 : ZMod 20011)
      decide
    · apply IsUnit.of_mul_eq_one (10183 : ZMod 20011)
      decide
    · apply IsUnit.of_mul_eq_one (4048 : ZMod 20011)
      decide
    · apply IsUnit.of_mul_eq_one (6463 : ZMod 20011)
      decide
    · apply IsUnit.of_mul_eq_one (3840 : ZMod 20011)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_20021 : Nat.Prime 20021 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 20021 20020 1 3 [2, 2, 5, 7, 11, 13]
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
    · apply IsUnit.of_mul_eq_one (10010 : ZMod 20021)
      decide
    · apply IsUnit.of_mul_eq_one (1923 : ZMod 20021)
      decide
    · apply IsUnit.of_mul_eq_one (3469 : ZMod 20021)
      decide
    · apply IsUnit.of_mul_eq_one (8566 : ZMod 20021)
      decide
    · apply IsUnit.of_mul_eq_one (6039 : ZMod 20021)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_20023 : Nat.Prime 20023 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 20023 20022 1 3 [2, 3, 47, 71]
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
    · apply IsUnit.of_mul_eq_one (10011 : ZMod 20023)
      decide
    · apply IsUnit.of_mul_eq_one (6721 : ZMod 20023)
      decide
    · apply IsUnit.of_mul_eq_one (5232 : ZMod 20023)
      decide
    · apply IsUnit.of_mul_eq_one (8693 : ZMod 20023)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_20029 : Nat.Prime 20029 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 20029 20028 1 2 [2, 2, 3, 1669]
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
    · apply IsUnit.of_mul_eq_one (10014 : ZMod 20029)
      decide
    · apply IsUnit.of_mul_eq_one (11111 : ZMod 20029)
      decide
    · apply IsUnit.of_mul_eq_one (494 : ZMod 20029)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_20047 : Nat.Prime 20047 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 20047 20046 1 3 [2, 3, 13, 257]
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
    · apply IsUnit.of_mul_eq_one (10023 : ZMod 20047)
      decide
    · apply IsUnit.of_mul_eq_one (13194 : ZMod 20047)
      decide
    · apply IsUnit.of_mul_eq_one (9866 : ZMod 20047)
      decide
    · apply IsUnit.of_mul_eq_one (16647 : ZMod 20047)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_20051 : Nat.Prime 20051 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 20051 20050 1 2 [2, 5, 5, 401]
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
    · apply IsUnit.of_mul_eq_one (10025 : ZMod 20051)
      decide
    · apply IsUnit.of_mul_eq_one (4472 : ZMod 20051)
      decide
    · apply IsUnit.of_mul_eq_one (13793 : ZMod 20051)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_20063 : Nat.Prime 20063 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 20063 20062 1 5 [2, 7, 1433]
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
    · apply IsUnit.of_mul_eq_one (10031 : ZMod 20063)
      decide
    · apply IsUnit.of_mul_eq_one (5916 : ZMod 20063)
      decide
    · apply IsUnit.of_mul_eq_one (4856 : ZMod 20063)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_20071 : Nat.Prime 20071 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 20071 20070 1 3 [2, 3, 3, 5, 223]
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
    · apply IsUnit.of_mul_eq_one (10035 : ZMod 20071)
      decide
    · apply IsUnit.of_mul_eq_one (8285 : ZMod 20071)
      decide
    · apply IsUnit.of_mul_eq_one (3700 : ZMod 20071)
      decide
    · apply IsUnit.of_mul_eq_one (17940 : ZMod 20071)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_20089 : Nat.Prime 20089 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 20089 20088 1 7 [2, 2, 2, 3, 3, 3, 3, 31]
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
    · apply IsUnit.of_mul_eq_one (10044 : ZMod 20089)
      decide
    · apply IsUnit.of_mul_eq_one (3974 : ZMod 20089)
      decide
    · apply IsUnit.of_mul_eq_one (6817 : ZMod 20089)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_20101 : Nat.Prime 20101 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 20101 20100 1 6 [2, 2, 3, 5, 5, 67]
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
    · apply IsUnit.of_mul_eq_one (10050 : ZMod 20101)
      decide
    · apply IsUnit.of_mul_eq_one (17996 : ZMod 20101)
      decide
    · apply IsUnit.of_mul_eq_one (9511 : ZMod 20101)
      decide
    · apply IsUnit.of_mul_eq_one (3422 : ZMod 20101)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_20107 : Nat.Prime 20107 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 20107 20106 1 2 [2, 3, 3, 1117]
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
    · apply IsUnit.of_mul_eq_one (10053 : ZMod 20107)
      decide
    · apply IsUnit.of_mul_eq_one (4380 : ZMod 20107)
      decide
    · apply IsUnit.of_mul_eq_one (10615 : ZMod 20107)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_20113 : Nat.Prime 20113 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 20113 20112 1 10 [2, 2, 2, 2, 3, 419]
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
    · apply IsUnit.of_mul_eq_one (10056 : ZMod 20113)
      decide
    · apply IsUnit.of_mul_eq_one (11584 : ZMod 20113)
      decide
    · apply IsUnit.of_mul_eq_one (9731 : ZMod 20113)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_20117 : Nat.Prime 20117 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 20117 20116 1 2 [2, 2, 47, 107]
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
    · apply IsUnit.of_mul_eq_one (10058 : ZMod 20117)
      decide
    · apply IsUnit.of_mul_eq_one (6602 : ZMod 20117)
      decide
    · apply IsUnit.of_mul_eq_one (14613 : ZMod 20117)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_20123 : Nat.Prime 20123 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 20123 20122 1 2 [2, 10061]
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
    · apply IsUnit.of_mul_eq_one (10061 : ZMod 20123)
      decide
    · apply IsUnit.of_mul_eq_one (6708 : ZMod 20123)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_20129 : Nat.Prime 20129 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 20129 20128 1 3 [2, 2, 2, 2, 2, 17, 37]
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
    · apply IsUnit.of_mul_eq_one (10064 : ZMod 20129)
      decide
    · apply IsUnit.of_mul_eq_one (15787 : ZMod 20129)
      decide
    · apply IsUnit.of_mul_eq_one (11635 : ZMod 20129)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_20143 : Nat.Prime 20143 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 20143 20142 1 5 [2, 3, 3, 3, 373]
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
    · apply IsUnit.of_mul_eq_one (10071 : ZMod 20143)
      decide
    · apply IsUnit.of_mul_eq_one (6839 : ZMod 20143)
      decide
    · apply IsUnit.of_mul_eq_one (7643 : ZMod 20143)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_20147 : Nat.Prime 20147 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 20147 20146 1 6 [2, 7, 1439]
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
    · apply IsUnit.of_mul_eq_one (10073 : ZMod 20147)
      decide
    · apply IsUnit.of_mul_eq_one (1299 : ZMod 20147)
      decide
    · apply IsUnit.of_mul_eq_one (12371 : ZMod 20147)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_20149 : Nat.Prime 20149 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 20149 20148 1 2 [2, 2, 3, 23, 73]
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
    · apply IsUnit.of_mul_eq_one (10074 : ZMod 20149)
      decide
    · apply IsUnit.of_mul_eq_one (4129 : ZMod 20149)
      decide
    · apply IsUnit.of_mul_eq_one (10732 : ZMod 20149)
      decide
    · apply IsUnit.of_mul_eq_one (4443 : ZMod 20149)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_20161 : Nat.Prime 20161 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 20161 20160 1 13 [2, 2, 2, 2, 2, 2, 3, 3, 5, 7]
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
    · apply IsUnit.of_mul_eq_one (10080 : ZMod 20161)
      decide
    · apply IsUnit.of_mul_eq_one (8778 : ZMod 20161)
      decide
    · apply IsUnit.of_mul_eq_one (4369 : ZMod 20161)
      decide
    · apply IsUnit.of_mul_eq_one (7310 : ZMod 20161)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_20173 : Nat.Prime 20173 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 20173 20172 1 2 [2, 2, 3, 41, 41]
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
    · apply IsUnit.of_mul_eq_one (10086 : ZMod 20173)
      decide
    · apply IsUnit.of_mul_eq_one (10045 : ZMod 20173)
      decide
    · apply IsUnit.of_mul_eq_one (5767 : ZMod 20173)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_20177 : Nat.Prime 20177 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 20177 20176 1 3 [2, 2, 2, 2, 13, 97]
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
    · apply IsUnit.of_mul_eq_one (10088 : ZMod 20177)
      decide
    · apply IsUnit.of_mul_eq_one (6366 : ZMod 20177)
      decide
    · apply IsUnit.of_mul_eq_one (1102 : ZMod 20177)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_20183 : Nat.Prime 20183 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 20183 20182 1 5 [2, 10091]
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
    · apply IsUnit.of_mul_eq_one (10091 : ZMod 20183)
      decide
    · apply IsUnit.of_mul_eq_one (841 : ZMod 20183)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_20201 : Nat.Prime 20201 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 20201 20200 1 6 [2, 2, 2, 5, 5, 101]
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
    · apply IsUnit.of_mul_eq_one (10100 : ZMod 20201)
      decide
    · apply IsUnit.of_mul_eq_one (9752 : ZMod 20201)
      decide
    · apply IsUnit.of_mul_eq_one (4621 : ZMod 20201)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_20219 : Nat.Prime 20219 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 20219 20218 1 2 [2, 11, 919]
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
    · apply IsUnit.of_mul_eq_one (10109 : ZMod 20219)
      decide
    · apply IsUnit.of_mul_eq_one (16500 : ZMod 20219)
      decide
    · apply IsUnit.of_mul_eq_one (14541 : ZMod 20219)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_20231 : Nat.Prime 20231 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 20231 20230 1 29 [2, 5, 7, 17, 17]
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
    · apply IsUnit.of_mul_eq_one (10115 : ZMod 20231)
      decide
    · apply IsUnit.of_mul_eq_one (1399 : ZMod 20231)
      decide
    · apply IsUnit.of_mul_eq_one (17148 : ZMod 20231)
      decide
    · apply IsUnit.of_mul_eq_one (5337 : ZMod 20231)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_20233 : Nat.Prime 20233 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 20233 20232 1 5 [2, 2, 2, 3, 3, 281]
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
    · apply IsUnit.of_mul_eq_one (10116 : ZMod 20233)
      decide
    · apply IsUnit.of_mul_eq_one (19074 : ZMod 20233)
      decide
    · apply IsUnit.of_mul_eq_one (18809 : ZMod 20233)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_20249 : Nat.Prime 20249 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 20249 20248 1 3 [2, 2, 2, 2531]
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
    · apply IsUnit.of_mul_eq_one (10124 : ZMod 20249)
      decide
    · apply IsUnit.of_mul_eq_one (4911 : ZMod 20249)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_20261 : Nat.Prime 20261 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 20261 20260 1 2 [2, 2, 5, 1013]
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
    · apply IsUnit.of_mul_eq_one (10130 : ZMod 20261)
      decide
    · apply IsUnit.of_mul_eq_one (2364 : ZMod 20261)
      decide
    · apply IsUnit.of_mul_eq_one (10984 : ZMod 20261)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_20269 : Nat.Prime 20269 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 20269 20268 1 2 [2, 2, 3, 3, 563]
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
    · apply IsUnit.of_mul_eq_one (10134 : ZMod 20269)
      decide
    · apply IsUnit.of_mul_eq_one (4932 : ZMod 20269)
      decide
    · apply IsUnit.of_mul_eq_one (1169 : ZMod 20269)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_20287 : Nat.Prime 20287 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 20287 20286 1 5 [2, 3, 3, 7, 7, 23]
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
    · apply IsUnit.of_mul_eq_one (10143 : ZMod 20287)
      decide
    · apply IsUnit.of_mul_eq_one (16027 : ZMod 20287)
      decide
    · apply IsUnit.of_mul_eq_one (8350 : ZMod 20287)
      decide
    · apply IsUnit.of_mul_eq_one (16878 : ZMod 20287)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_20297 : Nat.Prime 20297 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 20297 20296 1 3 [2, 2, 2, 43, 59]
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
    · apply IsUnit.of_mul_eq_one (10148 : ZMod 20297)
      decide
    · apply IsUnit.of_mul_eq_one (8084 : ZMod 20297)
      decide
    · apply IsUnit.of_mul_eq_one (10825 : ZMod 20297)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_20323 : Nat.Prime 20323 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 20323 20322 1 2 [2, 3, 3, 1129]
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
    · apply IsUnit.of_mul_eq_one (10161 : ZMod 20323)
      decide
    · apply IsUnit.of_mul_eq_one (3301 : ZMod 20323)
      decide
    · apply IsUnit.of_mul_eq_one (3430 : ZMod 20323)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_20327 : Nat.Prime 20327 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 20327 20326 1 5 [2, 10163]
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
    · apply IsUnit.of_mul_eq_one (10163 : ZMod 20327)
      decide
    · apply IsUnit.of_mul_eq_one (847 : ZMod 20327)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_20333 : Nat.Prime 20333 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 20333 20332 1 3 [2, 2, 13, 17, 23]
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
    · apply IsUnit.of_mul_eq_one (10166 : ZMod 20333)
      decide
    · apply IsUnit.of_mul_eq_one (2081 : ZMod 20333)
      decide
    · apply IsUnit.of_mul_eq_one (5054 : ZMod 20333)
      decide
    · apply IsUnit.of_mul_eq_one (16253 : ZMod 20333)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_20341 : Nat.Prime 20341 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 20341 20340 1 2 [2, 2, 3, 3, 5, 113]
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
    · apply IsUnit.of_mul_eq_one (10170 : ZMod 20341)
      decide
    · apply IsUnit.of_mul_eq_one (19555 : ZMod 20341)
      decide
    · apply IsUnit.of_mul_eq_one (9816 : ZMod 20341)
      decide
    · apply IsUnit.of_mul_eq_one (8869 : ZMod 20341)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_20347 : Nat.Prime 20347 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 20347 20346 1 3 [2, 3, 3391]
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
    · apply IsUnit.of_mul_eq_one (10173 : ZMod 20347)
      decide
    · apply IsUnit.of_mul_eq_one (13897 : ZMod 20347)
      decide
    · apply IsUnit.of_mul_eq_one (18698 : ZMod 20347)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_20353 : Nat.Prime 20353 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 20353 20352 1 5 [2, 2, 2, 2, 2, 2, 2, 3, 53]
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
    · apply IsUnit.of_mul_eq_one (10176 : ZMod 20353)
      decide
    · apply IsUnit.of_mul_eq_one (19058 : ZMod 20353)
      decide
    · apply IsUnit.of_mul_eq_one (3547 : ZMod 20353)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_20357 : Nat.Prime 20357 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 20357 20356 1 2 [2, 2, 7, 727]
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
    · apply IsUnit.of_mul_eq_one (10178 : ZMod 20357)
      decide
    · apply IsUnit.of_mul_eq_one (75 : ZMod 20357)
      decide
    · apply IsUnit.of_mul_eq_one (17546 : ZMod 20357)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_20359 : Nat.Prime 20359 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 20359 20358 1 11 [2, 3, 3, 3, 13, 29]
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
    · apply IsUnit.of_mul_eq_one (10179 : ZMod 20359)
      decide
    · apply IsUnit.of_mul_eq_one (9006 : ZMod 20359)
      decide
    · apply IsUnit.of_mul_eq_one (2012 : ZMod 20359)
      decide
    · apply IsUnit.of_mul_eq_one (11143 : ZMod 20359)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_20369 : Nat.Prime 20369 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 20369 20368 1 3 [2, 2, 2, 2, 19, 67]
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
    · apply IsUnit.of_mul_eq_one (10184 : ZMod 20369)
      decide
    · apply IsUnit.of_mul_eq_one (18587 : ZMod 20369)
      decide
    · apply IsUnit.of_mul_eq_one (12271 : ZMod 20369)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_20389 : Nat.Prime 20389 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 20389 20388 1 6 [2, 2, 3, 1699]
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
    · apply IsUnit.of_mul_eq_one (10194 : ZMod 20389)
      decide
    · apply IsUnit.of_mul_eq_one (7588 : ZMod 20389)
      decide
    · apply IsUnit.of_mul_eq_one (9215 : ZMod 20389)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_20393 : Nat.Prime 20393 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 20393 20392 1 3 [2, 2, 2, 2549]
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
    · apply IsUnit.of_mul_eq_one (10196 : ZMod 20393)
      decide
    · apply IsUnit.of_mul_eq_one (10268 : ZMod 20393)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_20399 : Nat.Prime 20399 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 20399 20398 1 7 [2, 7, 31, 47]
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
    · apply IsUnit.of_mul_eq_one (10199 : ZMod 20399)
      decide
    · apply IsUnit.of_mul_eq_one (10839 : ZMod 20399)
      decide
    · apply IsUnit.of_mul_eq_one (18124 : ZMod 20399)
      decide
    · apply IsUnit.of_mul_eq_one (11188 : ZMod 20399)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_20407 : Nat.Prime 20407 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 20407 20406 1 5 [2, 3, 19, 179]
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
    · apply IsUnit.of_mul_eq_one (10203 : ZMod 20407)
      decide
    · apply IsUnit.of_mul_eq_one (11712 : ZMod 20407)
      decide
    · apply IsUnit.of_mul_eq_one (17961 : ZMod 20407)
      decide
    · apply IsUnit.of_mul_eq_one (14218 : ZMod 20407)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_20411 : Nat.Prime 20411 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 20411 20410 1 6 [2, 5, 13, 157]
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
    · apply IsUnit.of_mul_eq_one (10205 : ZMod 20411)
      decide
    · apply IsUnit.of_mul_eq_one (4446 : ZMod 20411)
      decide
    · apply IsUnit.of_mul_eq_one (9910 : ZMod 20411)
      decide
    · apply IsUnit.of_mul_eq_one (12686 : ZMod 20411)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_20431 : Nat.Prime 20431 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 20431 20430 1 3 [2, 3, 3, 5, 227]
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
    · apply IsUnit.of_mul_eq_one (10215 : ZMod 20431)
      decide
    · apply IsUnit.of_mul_eq_one (2930 : ZMod 20431)
      decide
    · apply IsUnit.of_mul_eq_one (1686 : ZMod 20431)
      decide
    · apply IsUnit.of_mul_eq_one (2635 : ZMod 20431)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_20441 : Nat.Prime 20441 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 20441 20440 1 3 [2, 2, 2, 5, 7, 73]
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
    · apply IsUnit.of_mul_eq_one (10220 : ZMod 20441)
      decide
    · apply IsUnit.of_mul_eq_one (16809 : ZMod 20441)
      decide
    · apply IsUnit.of_mul_eq_one (432 : ZMod 20441)
      decide
    · apply IsUnit.of_mul_eq_one (13826 : ZMod 20441)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_20443 : Nat.Prime 20443 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 20443 20442 1 2 [2, 3, 3407]
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
    · apply IsUnit.of_mul_eq_one (10221 : ZMod 20443)
      decide
    · apply IsUnit.of_mul_eq_one (19114 : ZMod 20443)
      decide
    · apply IsUnit.of_mul_eq_one (649 : ZMod 20443)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_20477 : Nat.Prime 20477 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 20477 20476 1 2 [2, 2, 5119]
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
    · apply IsUnit.of_mul_eq_one (10238 : ZMod 20477)
      decide
    · apply IsUnit.of_mul_eq_one (9556 : ZMod 20477)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_20479 : Nat.Prime 20479 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 20479 20478 1 3 [2, 3, 3413]
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
    · apply IsUnit.of_mul_eq_one (10239 : ZMod 20479)
      decide
    · apply IsUnit.of_mul_eq_one (4355 : ZMod 20479)
      decide
    · apply IsUnit.of_mul_eq_one (19832 : ZMod 20479)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_20483 : Nat.Prime 20483 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 20483 20482 1 5 [2, 7, 7, 11, 19]
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
    · apply IsUnit.of_mul_eq_one (10241 : ZMod 20483)
      decide
    · apply IsUnit.of_mul_eq_one (3178 : ZMod 20483)
      decide
    · apply IsUnit.of_mul_eq_one (13475 : ZMod 20483)
      decide
    · apply IsUnit.of_mul_eq_one (13169 : ZMod 20483)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_20507 : Nat.Prime 20507 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 20507 20506 1 2 [2, 10253]
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
    · apply IsUnit.of_mul_eq_one (10253 : ZMod 20507)
      decide
    · apply IsUnit.of_mul_eq_one (6836 : ZMod 20507)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_20509 : Nat.Prime 20509 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 20509 20508 1 2 [2, 2, 3, 1709]
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
    · apply IsUnit.of_mul_eq_one (10254 : ZMod 20509)
      decide
    · apply IsUnit.of_mul_eq_one (2154 : ZMod 20509)
      decide
    · apply IsUnit.of_mul_eq_one (15080 : ZMod 20509)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_20521 : Nat.Prime 20521 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 20521 20520 1 11 [2, 2, 2, 3, 3, 3, 5, 19]
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
    · apply IsUnit.of_mul_eq_one (10260 : ZMod 20521)
      decide
    · apply IsUnit.of_mul_eq_one (7012 : ZMod 20521)
      decide
    · apply IsUnit.of_mul_eq_one (15971 : ZMod 20521)
      decide
    · apply IsUnit.of_mul_eq_one (11290 : ZMod 20521)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_20533 : Nat.Prime 20533 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 20533 20532 1 2 [2, 2, 3, 29, 59]
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
    · apply IsUnit.of_mul_eq_one (10266 : ZMod 20533)
      decide
    · apply IsUnit.of_mul_eq_one (19990 : ZMod 20533)
      decide
    · apply IsUnit.of_mul_eq_one (11583 : ZMod 20533)
      decide
    · apply IsUnit.of_mul_eq_one (7719 : ZMod 20533)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_20543 : Nat.Prime 20543 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 20543 20542 1 5 [2, 10271]
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
    · apply IsUnit.of_mul_eq_one (10271 : ZMod 20543)
      decide
    · apply IsUnit.of_mul_eq_one (856 : ZMod 20543)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_20549 : Nat.Prime 20549 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 20549 20548 1 2 [2, 2, 11, 467]
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
    · apply IsUnit.of_mul_eq_one (10274 : ZMod 20549)
      decide
    · apply IsUnit.of_mul_eq_one (5660 : ZMod 20549)
      decide
    · apply IsUnit.of_mul_eq_one (13173 : ZMod 20549)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_20551 : Nat.Prime 20551 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 20551 20550 1 3 [2, 3, 5, 5, 137]
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
    · apply IsUnit.of_mul_eq_one (10275 : ZMod 20551)
      decide
    · apply IsUnit.of_mul_eq_one (3570 : ZMod 20551)
      decide
    · apply IsUnit.of_mul_eq_one (7891 : ZMod 20551)
      decide
    · apply IsUnit.of_mul_eq_one (14162 : ZMod 20551)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_20563 : Nat.Prime 20563 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 20563 20562 1 3 [2, 3, 23, 149]
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
    · apply IsUnit.of_mul_eq_one (10281 : ZMod 20563)
      decide
    · apply IsUnit.of_mul_eq_one (5832 : ZMod 20563)
      decide
    · apply IsUnit.of_mul_eq_one (8692 : ZMod 20563)
      decide
    · apply IsUnit.of_mul_eq_one (11353 : ZMod 20563)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_20593 : Nat.Prime 20593 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 20593 20592 1 5 [2, 2, 2, 2, 3, 3, 11, 13]
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
    · apply IsUnit.of_mul_eq_one (10296 : ZMod 20593)
      decide
    · apply IsUnit.of_mul_eq_one (6816 : ZMod 20593)
      decide
    · apply IsUnit.of_mul_eq_one (1301 : ZMod 20593)
      decide
    · apply IsUnit.of_mul_eq_one (1862 : ZMod 20593)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_20599 : Nat.Prime 20599 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 20599 20598 1 3 [2, 3, 3433]
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
    · apply IsUnit.of_mul_eq_one (10299 : ZMod 20599)
      decide
    · apply IsUnit.of_mul_eq_one (4593 : ZMod 20599)
      decide
    · apply IsUnit.of_mul_eq_one (5461 : ZMod 20599)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_20611 : Nat.Prime 20611 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 20611 20610 1 2 [2, 3, 3, 5, 229]
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
    · apply IsUnit.of_mul_eq_one (10305 : ZMod 20611)
      decide
    · apply IsUnit.of_mul_eq_one (1364 : ZMod 20611)
      decide
    · apply IsUnit.of_mul_eq_one (19094 : ZMod 20611)
      decide
    · apply IsUnit.of_mul_eq_one (13083 : ZMod 20611)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_20627 : Nat.Prime 20627 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 20627 20626 1 2 [2, 10313]
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
    · apply IsUnit.of_mul_eq_one (10313 : ZMod 20627)
      decide
    · apply IsUnit.of_mul_eq_one (6876 : ZMod 20627)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_20639 : Nat.Prime 20639 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 20639 20638 1 11 [2, 17, 607]
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
    · apply IsUnit.of_mul_eq_one (10319 : ZMod 20639)
      decide
    · apply IsUnit.of_mul_eq_one (20403 : ZMod 20639)
      decide
    · apply IsUnit.of_mul_eq_one (8230 : ZMod 20639)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_20641 : Nat.Prime 20641 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 20641 20640 1 7 [2, 2, 2, 2, 2, 3, 5, 43]
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
    · apply IsUnit.of_mul_eq_one (10320 : ZMod 20641)
      decide
    · apply IsUnit.of_mul_eq_one (9887 : ZMod 20641)
      decide
    · apply IsUnit.of_mul_eq_one (17671 : ZMod 20641)
      decide
    · apply IsUnit.of_mul_eq_one (18608 : ZMod 20641)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_20663 : Nat.Prime 20663 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 20663 20662 1 5 [2, 10331]
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
    · apply IsUnit.of_mul_eq_one (10331 : ZMod 20663)
      decide
    · apply IsUnit.of_mul_eq_one (861 : ZMod 20663)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_20681 : Nat.Prime 20681 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 20681 20680 1 3 [2, 2, 2, 5, 11, 47]
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
    · apply IsUnit.of_mul_eq_one (10340 : ZMod 20681)
      decide
    · apply IsUnit.of_mul_eq_one (269 : ZMod 20681)
      decide
    · apply IsUnit.of_mul_eq_one (2471 : ZMod 20681)
      decide
    · apply IsUnit.of_mul_eq_one (16157 : ZMod 20681)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_20693 : Nat.Prime 20693 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 20693 20692 1 2 [2, 2, 7, 739]
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
    · apply IsUnit.of_mul_eq_one (10346 : ZMod 20693)
      decide
    · apply IsUnit.of_mul_eq_one (17693 : ZMod 20693)
      decide
    · apply IsUnit.of_mul_eq_one (3606 : ZMod 20693)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_20707 : Nat.Prime 20707 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 20707 20706 1 5 [2, 3, 7, 17, 29]
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
    · apply IsUnit.of_mul_eq_one (10353 : ZMod 20707)
      decide
    · apply IsUnit.of_mul_eq_one (8734 : ZMod 20707)
      decide
    · apply IsUnit.of_mul_eq_one (10766 : ZMod 20707)
      decide
    · apply IsUnit.of_mul_eq_one (14122 : ZMod 20707)
      decide
    · apply IsUnit.of_mul_eq_one (8678 : ZMod 20707)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_20717 : Nat.Prime 20717 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 20717 20716 1 2 [2, 2, 5179]
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
    · apply IsUnit.of_mul_eq_one (10358 : ZMod 20717)
      decide
    · apply IsUnit.of_mul_eq_one (9668 : ZMod 20717)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_20719 : Nat.Prime 20719 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 20719 20718 1 3 [2, 3, 3, 1151]
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
    · apply IsUnit.of_mul_eq_one (10359 : ZMod 20719)
      decide
    · apply IsUnit.of_mul_eq_one (5847 : ZMod 20719)
      decide
    · apply IsUnit.of_mul_eq_one (2855 : ZMod 20719)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_20731 : Nat.Prime 20731 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 20731 20730 1 2 [2, 3, 5, 691]
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
    · apply IsUnit.of_mul_eq_one (10365 : ZMod 20731)
      decide
    · apply IsUnit.of_mul_eq_one (1290 : ZMod 20731)
      decide
    · apply IsUnit.of_mul_eq_one (18705 : ZMod 20731)
      decide
    · apply IsUnit.of_mul_eq_one (14091 : ZMod 20731)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_20743 : Nat.Prime 20743 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 20743 20742 1 5 [2, 3, 3457]
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
    · apply IsUnit.of_mul_eq_one (10371 : ZMod 20743)
      decide
    · apply IsUnit.of_mul_eq_one (10261 : ZMod 20743)
      decide
    · apply IsUnit.of_mul_eq_one (2253 : ZMod 20743)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_20747 : Nat.Prime 20747 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 20747 20746 1 5 [2, 11, 23, 41]
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
    · apply IsUnit.of_mul_eq_one (10373 : ZMod 20747)
      decide
    · apply IsUnit.of_mul_eq_one (18178 : ZMod 20747)
      decide
    · apply IsUnit.of_mul_eq_one (12531 : ZMod 20747)
      decide
    · apply IsUnit.of_mul_eq_one (16397 : ZMod 20747)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_20749 : Nat.Prime 20749 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 20749 20748 1 2 [2, 2, 3, 7, 13, 19]
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
    · apply IsUnit.of_mul_eq_one (10374 : ZMod 20749)
      decide
    · apply IsUnit.of_mul_eq_one (5876 : ZMod 20749)
      decide
    · apply IsUnit.of_mul_eq_one (13870 : ZMod 20749)
      decide
    · apply IsUnit.of_mul_eq_one (1786 : ZMod 20749)
      decide
    · apply IsUnit.of_mul_eq_one (19932 : ZMod 20749)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_20753 : Nat.Prime 20753 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 20753 20752 1 3 [2, 2, 2, 2, 1297]
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
    · apply IsUnit.of_mul_eq_one (10376 : ZMod 20753)
      decide
    · apply IsUnit.of_mul_eq_one (7254 : ZMod 20753)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_20759 : Nat.Prime 20759 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 20759 20758 1 7 [2, 97, 107]
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
    · apply IsUnit.of_mul_eq_one (10379 : ZMod 20759)
      decide
    · apply IsUnit.of_mul_eq_one (15464 : ZMod 20759)
      decide
    · apply IsUnit.of_mul_eq_one (1218 : ZMod 20759)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_20771 : Nat.Prime 20771 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 20771 20770 1 2 [2, 5, 31, 67]
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
    · apply IsUnit.of_mul_eq_one (10385 : ZMod 20771)
      decide
    · apply IsUnit.of_mul_eq_one (13327 : ZMod 20771)
      decide
    · apply IsUnit.of_mul_eq_one (17947 : ZMod 20771)
      decide
    · apply IsUnit.of_mul_eq_one (7321 : ZMod 20771)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_20773 : Nat.Prime 20773 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 20773 20772 1 2 [2, 2, 3, 3, 577]
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
    · apply IsUnit.of_mul_eq_one (10386 : ZMod 20773)
      decide
    · apply IsUnit.of_mul_eq_one (7397 : ZMod 20773)
      decide
    · apply IsUnit.of_mul_eq_one (449 : ZMod 20773)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_20789 : Nat.Prime 20789 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 20789 20788 1 2 [2, 2, 5197]
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
    · apply IsUnit.of_mul_eq_one (10394 : ZMod 20789)
      decide
    · apply IsUnit.of_mul_eq_one (1386 : ZMod 20789)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_20807 : Nat.Prime 20807 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 20807 20806 1 5 [2, 101, 103]
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
    · apply IsUnit.of_mul_eq_one (10403 : ZMod 20807)
      decide
    · apply IsUnit.of_mul_eq_one (12422 : ZMod 20807)
      decide
    · apply IsUnit.of_mul_eq_one (10913 : ZMod 20807)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_20809 : Nat.Prime 20809 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 20809 20808 1 7 [2, 2, 2, 3, 3, 17, 17]
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
    · apply IsUnit.of_mul_eq_one (10404 : ZMod 20809)
      decide
    · apply IsUnit.of_mul_eq_one (14283 : ZMod 20809)
      decide
    · apply IsUnit.of_mul_eq_one (4492 : ZMod 20809)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_20849 : Nat.Prime 20849 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 20849 20848 1 3 [2, 2, 2, 2, 1303]
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
    · apply IsUnit.of_mul_eq_one (10424 : ZMod 20849)
      decide
    · apply IsUnit.of_mul_eq_one (17508 : ZMod 20849)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_20857 : Nat.Prime 20857 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 20857 20856 1 10 [2, 2, 2, 3, 11, 79]
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
    · apply IsUnit.of_mul_eq_one (10428 : ZMod 20857)
      decide
    · apply IsUnit.of_mul_eq_one (20174 : ZMod 20857)
      decide
    · apply IsUnit.of_mul_eq_one (19492 : ZMod 20857)
      decide
    · apply IsUnit.of_mul_eq_one (6199 : ZMod 20857)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_20873 : Nat.Prime 20873 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 20873 20872 1 3 [2, 2, 2, 2609]
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
    · apply IsUnit.of_mul_eq_one (10436 : ZMod 20873)
      decide
    · apply IsUnit.of_mul_eq_one (6946 : ZMod 20873)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_20879 : Nat.Prime 20879 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 20879 20878 1 11 [2, 11, 13, 73]
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
    · apply IsUnit.of_mul_eq_one (10439 : ZMod 20879)
      decide
    · apply IsUnit.of_mul_eq_one (5284 : ZMod 20879)
      decide
    · apply IsUnit.of_mul_eq_one (12983 : ZMod 20879)
      decide
    · apply IsUnit.of_mul_eq_one (13333 : ZMod 20879)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_20887 : Nat.Prime 20887 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 20887 20886 1 3 [2, 3, 59, 59]
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
    · apply IsUnit.of_mul_eq_one (10443 : ZMod 20887)
      decide
    · apply IsUnit.of_mul_eq_one (4625 : ZMod 20887)
      decide
    · apply IsUnit.of_mul_eq_one (16729 : ZMod 20887)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_20897 : Nat.Prime 20897 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 20897 20896 1 3 [2, 2, 2, 2, 2, 653]
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
    · apply IsUnit.of_mul_eq_one (10448 : ZMod 20897)
      decide
    · apply IsUnit.of_mul_eq_one (4574 : ZMod 20897)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_20899 : Nat.Prime 20899 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 20899 20898 1 2 [2, 3, 3, 3, 3, 3, 43]
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
    · apply IsUnit.of_mul_eq_one (10449 : ZMod 20899)
      decide
    · apply IsUnit.of_mul_eq_one (9762 : ZMod 20899)
      decide
    · apply IsUnit.of_mul_eq_one (17050 : ZMod 20899)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_20903 : Nat.Prime 20903 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 20903 20902 1 5 [2, 7, 1493]
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
    · apply IsUnit.of_mul_eq_one (10451 : ZMod 20903)
      decide
    · apply IsUnit.of_mul_eq_one (2666 : ZMod 20903)
      decide
    · apply IsUnit.of_mul_eq_one (7744 : ZMod 20903)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_20921 : Nat.Prime 20921 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 20921 20920 1 3 [2, 2, 2, 5, 523]
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
    · apply IsUnit.of_mul_eq_one (10460 : ZMod 20921)
      decide
    · apply IsUnit.of_mul_eq_one (20657 : ZMod 20921)
      decide
    · apply IsUnit.of_mul_eq_one (13366 : ZMod 20921)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_20929 : Nat.Prime 20929 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 20929 20928 1 7 [2, 2, 2, 2, 2, 2, 3, 109]
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
    · apply IsUnit.of_mul_eq_one (10464 : ZMod 20929)
      decide
    · apply IsUnit.of_mul_eq_one (8981 : ZMod 20929)
      decide
    · apply IsUnit.of_mul_eq_one (12666 : ZMod 20929)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_20939 : Nat.Prime 20939 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 20939 20938 1 2 [2, 19, 19, 29]
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
    · apply IsUnit.of_mul_eq_one (10469 : ZMod 20939)
      decide
    · apply IsUnit.of_mul_eq_one (18401 : ZMod 20939)
      decide
    · apply IsUnit.of_mul_eq_one (14100 : ZMod 20939)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_20947 : Nat.Prime 20947 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 20947 20946 1 3 [2, 3, 3491]
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
    · apply IsUnit.of_mul_eq_one (10473 : ZMod 20947)
      decide
    · apply IsUnit.of_mul_eq_one (7609 : ZMod 20947)
      decide
    · apply IsUnit.of_mul_eq_one (18789 : ZMod 20947)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_20959 : Nat.Prime 20959 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 20959 20958 1 7 [2, 3, 7, 499]
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
    · apply IsUnit.of_mul_eq_one (10479 : ZMod 20959)
      decide
    · apply IsUnit.of_mul_eq_one (6442 : ZMod 20959)
      decide
    · apply IsUnit.of_mul_eq_one (3993 : ZMod 20959)
      decide
    · apply IsUnit.of_mul_eq_one (14799 : ZMod 20959)
      decide
  · norm_num
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_19937_20958_part02 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_20952 (p := 19997) (q := 20011) (by exact lowPrime_20011) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_20952 (p := 20011) (q := 20021) (by exact lowPrime_20021) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_20952 (p := 20021) (q := 20023) (by exact lowPrime_20023) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_20952 (p := 20023) (q := 20029) (by exact lowPrime_20029) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_20952 (p := 20029) (q := 20047) (by exact lowPrime_20047) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_20952 (p := 20047) (q := 20051) (by exact lowPrime_20051) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_20952 (p := 20051) (q := 20063) (by exact lowPrime_20063) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_20952 (p := 20063) (q := 20071) (by exact lowPrime_20071) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_19937_20958_part02_chain :
    DusartPrimeRowsChain 19997 20070 dusartPrimeRows_19937_20958_part02 := by
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

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_19937_20958_part03 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_20952 (p := 20071) (q := 20089) (by exact lowPrime_20089) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_20952 (p := 20089) (q := 20101) (by exact lowPrime_20101) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_20952 (p := 20101) (q := 20107) (by exact lowPrime_20107) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_20952 (p := 20107) (q := 20113) (by exact lowPrime_20113) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_20952 (p := 20113) (q := 20117) (by exact lowPrime_20117) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_20952 (p := 20117) (q := 20123) (by exact lowPrime_20123) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_20952 (p := 20123) (q := 20129) (by exact lowPrime_20129) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_20952 (p := 20129) (q := 20143) (by exact lowPrime_20143) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_19937_20958_part03_chain :
    DusartPrimeRowsChain 20071 20142 dusartPrimeRows_19937_20958_part03 := by
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

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_19937_20958_part04 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_20952 (p := 20143) (q := 20147) (by exact lowPrime_20147) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_20952 (p := 20147) (q := 20149) (by exact lowPrime_20149) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_20952 (p := 20149) (q := 20161) (by exact lowPrime_20161) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_20952 (p := 20161) (q := 20173) (by exact lowPrime_20173) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_20952 (p := 20173) (q := 20177) (by exact lowPrime_20177) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_20952 (p := 20177) (q := 20183) (by exact lowPrime_20183) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_20952 (p := 20183) (q := 20201) (by exact lowPrime_20201) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_20952 (p := 20201) (q := 20219) (by exact lowPrime_20219) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_19937_20958_part04_chain :
    DusartPrimeRowsChain 20143 20218 dusartPrimeRows_19937_20958_part04 := by
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

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_19937_20958_part05 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_20952 (p := 20219) (q := 20231) (by exact lowPrime_20231) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_20952 (p := 20231) (q := 20233) (by exact lowPrime_20233) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_20952 (p := 20233) (q := 20249) (by exact lowPrime_20249) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_20952 (p := 20249) (q := 20261) (by exact lowPrime_20261) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_20952 (p := 20261) (q := 20269) (by exact lowPrime_20269) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_20952 (p := 20269) (q := 20287) (by exact lowPrime_20287) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_20952 (p := 20287) (q := 20297) (by exact lowPrime_20297) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_20952 (p := 20297) (q := 20323) (by exact lowPrime_20323) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_19937_20958_part05_chain :
    DusartPrimeRowsChain 20219 20322 dusartPrimeRows_19937_20958_part05 := by
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

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_19937_20958_part06 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_20952 (p := 20323) (q := 20327) (by exact lowPrime_20327) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_20952 (p := 20327) (q := 20333) (by exact lowPrime_20333) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_20952 (p := 20333) (q := 20341) (by exact lowPrime_20341) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_20952 (p := 20341) (q := 20347) (by exact lowPrime_20347) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_20952 (p := 20347) (q := 20353) (by exact lowPrime_20353) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_20952 (p := 20353) (q := 20357) (by exact lowPrime_20357) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_20952 (p := 20357) (q := 20359) (by exact lowPrime_20359) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_20952 (p := 20359) (q := 20369) (by exact lowPrime_20369) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_19937_20958_part06_chain :
    DusartPrimeRowsChain 20323 20368 dusartPrimeRows_19937_20958_part06 := by
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

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_19937_20958_part07 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_20952 (p := 20369) (q := 20389) (by exact lowPrime_20389) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_20952 (p := 20389) (q := 20393) (by exact lowPrime_20393) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_20952 (p := 20393) (q := 20399) (by exact lowPrime_20399) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_20952 (p := 20399) (q := 20407) (by exact lowPrime_20407) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_20952 (p := 20407) (q := 20411) (by exact lowPrime_20411) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_20952 (p := 20411) (q := 20431) (by exact lowPrime_20431) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_20952 (p := 20431) (q := 20441) (by exact lowPrime_20441) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_20952 (p := 20441) (q := 20443) (by exact lowPrime_20443) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_19937_20958_part07_chain :
    DusartPrimeRowsChain 20369 20442 dusartPrimeRows_19937_20958_part07 := by
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

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_19937_20958_part08 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_20952 (p := 20443) (q := 20477) (by exact lowPrime_20477) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_20952 (p := 20477) (q := 20479) (by exact lowPrime_20479) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_20952 (p := 20479) (q := 20483) (by exact lowPrime_20483) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_20952 (p := 20483) (q := 20507) (by exact lowPrime_20507) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_20952 (p := 20507) (q := 20509) (by exact lowPrime_20509) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_20952 (p := 20509) (q := 20521) (by exact lowPrime_20521) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_20952 (p := 20521) (q := 20533) (by exact lowPrime_20533) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_20952 (p := 20533) (q := 20543) (by exact lowPrime_20543) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_19937_20958_part08_chain :
    DusartPrimeRowsChain 20443 20542 dusartPrimeRows_19937_20958_part08 := by
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

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_19937_20958_part09 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_20952 (p := 20543) (q := 20549) (by exact lowPrime_20549) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_20952 (p := 20549) (q := 20551) (by exact lowPrime_20551) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_20952 (p := 20551) (q := 20563) (by exact lowPrime_20563) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_20952 (p := 20563) (q := 20593) (by exact lowPrime_20593) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_20952 (p := 20593) (q := 20599) (by exact lowPrime_20599) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_20952 (p := 20599) (q := 20611) (by exact lowPrime_20611) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_20952 (p := 20611) (q := 20627) (by exact lowPrime_20627) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_20952 (p := 20627) (q := 20639) (by exact lowPrime_20639) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_19937_20958_part09_chain :
    DusartPrimeRowsChain 20543 20638 dusartPrimeRows_19937_20958_part09 := by
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

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_19937_20958_part10 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_20952 (p := 20639) (q := 20641) (by exact lowPrime_20641) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_20952 (p := 20641) (q := 20663) (by exact lowPrime_20663) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_20952 (p := 20663) (q := 20681) (by exact lowPrime_20681) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_20952 (p := 20681) (q := 20693) (by exact lowPrime_20693) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_20952 (p := 20693) (q := 20707) (by exact lowPrime_20707) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_20952 (p := 20707) (q := 20717) (by exact lowPrime_20717) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_20952 (p := 20717) (q := 20719) (by exact lowPrime_20719) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_20952 (p := 20719) (q := 20731) (by exact lowPrime_20731) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_19937_20958_part10_chain :
    DusartPrimeRowsChain 20639 20730 dusartPrimeRows_19937_20958_part10 := by
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

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_19937_20958_part11 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_20952 (p := 20731) (q := 20743) (by exact lowPrime_20743) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_20952 (p := 20743) (q := 20747) (by exact lowPrime_20747) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_20952 (p := 20747) (q := 20749) (by exact lowPrime_20749) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_20952 (p := 20749) (q := 20753) (by exact lowPrime_20753) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_20952 (p := 20753) (q := 20759) (by exact lowPrime_20759) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_20952 (p := 20759) (q := 20771) (by exact lowPrime_20771) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_20952 (p := 20771) (q := 20773) (by exact lowPrime_20773) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_20952 (p := 20773) (q := 20789) (by exact lowPrime_20789) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_19937_20958_part11_chain :
    DusartPrimeRowsChain 20731 20788 dusartPrimeRows_19937_20958_part11 := by
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

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_19937_20958_part12 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_20952 (p := 20789) (q := 20807) (by exact lowPrime_20807) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_20952 (p := 20807) (q := 20809) (by exact lowPrime_20809) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_20952 (p := 20809) (q := 20849) (by exact lowPrime_20849) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_20952 (p := 20849) (q := 20857) (by exact lowPrime_20857) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_20952 (p := 20857) (q := 20873) (by exact lowPrime_20873) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_20952 (p := 20873) (q := 20879) (by exact lowPrime_20879) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_20952 (p := 20879) (q := 20887) (by exact lowPrime_20887) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_20952 (p := 20887) (q := 20897) (by exact lowPrime_20897) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_19937_20958_part12_chain :
    DusartPrimeRowsChain 20789 20896 dusartPrimeRows_19937_20958_part12 := by
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

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_19937_20958_part13 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_20952 (p := 20897) (q := 20899) (by exact lowPrime_20899) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_20952 (p := 20899) (q := 20903) (by exact lowPrime_20903) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_20952 (p := 20903) (q := 20921) (by exact lowPrime_20921) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_20952 (p := 20921) (q := 20929) (by exact lowPrime_20929) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_20952 (p := 20929) (q := 20939) (by exact lowPrime_20939) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_20952 (p := 20939) (q := 20947) (by exact lowPrime_20947) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_20952 (p := 20947) (q := 20959) (by exact lowPrime_20959) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_19937_20958_part13_chain :
    DusartPrimeRowsChain 20897 20958 dusartPrimeRows_19937_20958_part13 := by
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
              · apply DusartPrimeRowsChain.empty
                norm_num [dusartPrimeRow_of_explicit_20952, dusartPrimeRow_of_explicit_right]
