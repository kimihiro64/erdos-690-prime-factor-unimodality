import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowBase

set_option autoImplicit false
set_option maxRecDepth 1000000

/-! # Lower finite Dusart prefix chunk 03 -/

namespace PrimeFactorUnimodality

noncomputable section
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_4817 : Nat.Prime 4817 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 4817 4816 1 3 [2, 2, 2, 2, 7, 43]
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
    · apply IsUnit.of_mul_eq_one (2408 : ZMod 4817)
      decide
    · apply IsUnit.of_mul_eq_one (2310 : ZMod 4817)
      decide
    · apply IsUnit.of_mul_eq_one (4804 : ZMod 4817)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_4831 : Nat.Prime 4831 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 4831 4830 1 3 [2, 3, 5, 7, 23]
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
    · apply IsUnit.of_mul_eq_one (2415 : ZMod 4831)
      decide
    · apply IsUnit.of_mul_eq_one (1633 : ZMod 4831)
      decide
    · apply IsUnit.of_mul_eq_one (3287 : ZMod 4831)
      decide
    · apply IsUnit.of_mul_eq_one (1231 : ZMod 4831)
      decide
    · apply IsUnit.of_mul_eq_one (1412 : ZMod 4831)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_4861 : Nat.Prime 4861 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 4861 4860 1 11 [2, 2, 3, 3, 3, 3, 3, 5]
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
    · apply IsUnit.of_mul_eq_one (2430 : ZMod 4861)
      decide
    · apply IsUnit.of_mul_eq_one (106 : ZMod 4861)
      decide
    · apply IsUnit.of_mul_eq_one (4154 : ZMod 4861)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_4871 : Nat.Prime 4871 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 4871 4870 1 11 [2, 5, 487]
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
    · apply IsUnit.of_mul_eq_one (2435 : ZMod 4871)
      decide
    · apply IsUnit.of_mul_eq_one (898 : ZMod 4871)
      decide
    · apply IsUnit.of_mul_eq_one (3989 : ZMod 4871)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_4877 : Nat.Prime 4877 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 4877 4876 1 2 [2, 2, 23, 53]
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
    · apply IsUnit.of_mul_eq_one (2438 : ZMod 4877)
      decide
    · apply IsUnit.of_mul_eq_one (3871 : ZMod 4877)
      decide
    · apply IsUnit.of_mul_eq_one (326 : ZMod 4877)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_4889 : Nat.Prime 4889 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 4889 4888 1 3 [2, 2, 2, 13, 47]
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
    · apply IsUnit.of_mul_eq_one (2444 : ZMod 4889)
      decide
    · apply IsUnit.of_mul_eq_one (3584 : ZMod 4889)
      decide
    · apply IsUnit.of_mul_eq_one (4116 : ZMod 4889)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_4903 : Nat.Prime 4903 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 4903 4902 1 3 [2, 3, 19, 43]
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
    · apply IsUnit.of_mul_eq_one (2451 : ZMod 4903)
      decide
    · apply IsUnit.of_mul_eq_one (805 : ZMod 4903)
      decide
    · apply IsUnit.of_mul_eq_one (1009 : ZMod 4903)
      decide
    · apply IsUnit.of_mul_eq_one (788 : ZMod 4903)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_4909 : Nat.Prime 4909 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 4909 4908 1 6 [2, 2, 3, 409]
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
    · apply IsUnit.of_mul_eq_one (2454 : ZMod 4909)
      decide
    · apply IsUnit.of_mul_eq_one (1827 : ZMod 4909)
      decide
    · apply IsUnit.of_mul_eq_one (322 : ZMod 4909)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_4919 : Nat.Prime 4919 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 4919 4918 1 13 [2, 2459]
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
    · apply IsUnit.of_mul_eq_one (2459 : ZMod 4919)
      decide
    · apply IsUnit.of_mul_eq_one (732 : ZMod 4919)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_4931 : Nat.Prime 4931 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 4931 4930 1 6 [2, 5, 17, 29]
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
    · apply IsUnit.of_mul_eq_one (2465 : ZMod 4931)
      decide
    · apply IsUnit.of_mul_eq_one (3280 : ZMod 4931)
      decide
    · apply IsUnit.of_mul_eq_one (583 : ZMod 4931)
      decide
    · apply IsUnit.of_mul_eq_one (3570 : ZMod 4931)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_4933 : Nat.Prime 4933 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 4933 4932 1 2 [2, 2, 3, 3, 137]
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
    · apply IsUnit.of_mul_eq_one (2466 : ZMod 4933)
      decide
    · apply IsUnit.of_mul_eq_one (4222 : ZMod 4933)
      decide
    · apply IsUnit.of_mul_eq_one (4175 : ZMod 4933)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_4937 : Nat.Prime 4937 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 4937 4936 1 3 [2, 2, 2, 617]
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
    · apply IsUnit.of_mul_eq_one (2468 : ZMod 4937)
      decide
    · apply IsUnit.of_mul_eq_one (1089 : ZMod 4937)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_4943 : Nat.Prime 4943 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 4943 4942 1 7 [2, 7, 353]
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
    · apply IsUnit.of_mul_eq_one (2471 : ZMod 4943)
      decide
    · apply IsUnit.of_mul_eq_one (3905 : ZMod 4943)
      decide
    · apply IsUnit.of_mul_eq_one (2315 : ZMod 4943)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_4951 : Nat.Prime 4951 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 4951 4950 1 6 [2, 3, 3, 5, 5, 11]
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
    · apply IsUnit.of_mul_eq_one (2475 : ZMod 4951)
      decide
    · apply IsUnit.of_mul_eq_one (896 : ZMod 4951)
      decide
    · apply IsUnit.of_mul_eq_one (660 : ZMod 4951)
      decide
    · apply IsUnit.of_mul_eq_one (320 : ZMod 4951)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_4957 : Nat.Prime 4957 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 4957 4956 1 2 [2, 2, 3, 7, 59]
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
    · apply IsUnit.of_mul_eq_one (2478 : ZMod 4957)
      decide
    · apply IsUnit.of_mul_eq_one (4065 : ZMod 4957)
      decide
    · apply IsUnit.of_mul_eq_one (4911 : ZMod 4957)
      decide
    · apply IsUnit.of_mul_eq_one (483 : ZMod 4957)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_4967 : Nat.Prime 4967 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 4967 4966 1 5 [2, 13, 191]
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
    · apply IsUnit.of_mul_eq_one (2483 : ZMod 4967)
      decide
    · apply IsUnit.of_mul_eq_one (755 : ZMod 4967)
      decide
    · apply IsUnit.of_mul_eq_one (1551 : ZMod 4967)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_4969 : Nat.Prime 4969 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 4969 4968 1 11 [2, 2, 2, 3, 3, 3, 23]
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
    · apply IsUnit.of_mul_eq_one (2484 : ZMod 4969)
      decide
    · apply IsUnit.of_mul_eq_one (1718 : ZMod 4969)
      decide
    · apply IsUnit.of_mul_eq_one (4585 : ZMod 4969)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_4973 : Nat.Prime 4973 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 4973 4972 1 2 [2, 2, 11, 113]
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
    · apply IsUnit.of_mul_eq_one (2486 : ZMod 4973)
      decide
    · apply IsUnit.of_mul_eq_one (1889 : ZMod 4973)
      decide
    · apply IsUnit.of_mul_eq_one (604 : ZMod 4973)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_4987 : Nat.Prime 4987 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 4987 4986 1 2 [2, 3, 3, 277]
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
    · apply IsUnit.of_mul_eq_one (2493 : ZMod 4987)
      decide
    · apply IsUnit.of_mul_eq_one (3703 : ZMod 4987)
      decide
    · apply IsUnit.of_mul_eq_one (835 : ZMod 4987)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_4993 : Nat.Prime 4993 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 4993 4992 1 5 [2, 2, 2, 2, 2, 2, 2, 3, 13]
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
    · apply IsUnit.of_mul_eq_one (2496 : ZMod 4993)
      decide
    · apply IsUnit.of_mul_eq_one (4109 : ZMod 4993)
      decide
    · apply IsUnit.of_mul_eq_one (4169 : ZMod 4993)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_4999 : Nat.Prime 4999 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 4999 4998 1 3 [2, 3, 7, 7, 17]
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
    · apply IsUnit.of_mul_eq_one (2499 : ZMod 4999)
      decide
    · apply IsUnit.of_mul_eq_one (2445 : ZMod 4999)
      decide
    · apply IsUnit.of_mul_eq_one (3517 : ZMod 4999)
      decide
    · apply IsUnit.of_mul_eq_one (3757 : ZMod 4999)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_5003 : Nat.Prime 5003 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 5003 5002 1 2 [2, 41, 61]
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
    · apply IsUnit.of_mul_eq_one (2501 : ZMod 5003)
      decide
    · apply IsUnit.of_mul_eq_one (3107 : ZMod 5003)
      decide
    · apply IsUnit.of_mul_eq_one (4341 : ZMod 5003)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_5009 : Nat.Prime 5009 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 5009 5008 1 3 [2, 2, 2, 2, 313]
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
    · apply IsUnit.of_mul_eq_one (2504 : ZMod 5009)
      decide
    · apply IsUnit.of_mul_eq_one (8 : ZMod 5009)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_5011 : Nat.Prime 5011 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 5011 5010 1 2 [2, 3, 5, 167]
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
    · apply IsUnit.of_mul_eq_one (2505 : ZMod 5011)
      decide
    · apply IsUnit.of_mul_eq_one (2371 : ZMod 5011)
      decide
    · apply IsUnit.of_mul_eq_one (2745 : ZMod 5011)
      decide
    · apply IsUnit.of_mul_eq_one (604 : ZMod 5011)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_5021 : Nat.Prime 5021 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 5021 5020 1 3 [2, 2, 5, 251]
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
    · apply IsUnit.of_mul_eq_one (2510 : ZMod 5021)
      decide
    · apply IsUnit.of_mul_eq_one (571 : ZMod 5021)
      decide
    · apply IsUnit.of_mul_eq_one (3545 : ZMod 5021)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_5023 : Nat.Prime 5023 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 5023 5022 1 3 [2, 3, 3, 3, 3, 31]
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
    · apply IsUnit.of_mul_eq_one (2511 : ZMod 5023)
      decide
    · apply IsUnit.of_mul_eq_one (1356 : ZMod 5023)
      decide
    · apply IsUnit.of_mul_eq_one (4048 : ZMod 5023)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_5039 : Nat.Prime 5039 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 5039 5038 1 11 [2, 11, 229]
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
    · apply IsUnit.of_mul_eq_one (2519 : ZMod 5039)
      decide
    · apply IsUnit.of_mul_eq_one (3953 : ZMod 5039)
      decide
    · apply IsUnit.of_mul_eq_one (874 : ZMod 5039)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_5051 : Nat.Prime 5051 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 5051 5050 1 2 [2, 5, 5, 101]
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
    · apply IsUnit.of_mul_eq_one (2525 : ZMod 5051)
      decide
    · apply IsUnit.of_mul_eq_one (3446 : ZMod 5051)
      decide
    · apply IsUnit.of_mul_eq_one (2703 : ZMod 5051)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_5059 : Nat.Prime 5059 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 5059 5058 1 2 [2, 3, 3, 281]
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
    · apply IsUnit.of_mul_eq_one (2529 : ZMod 5059)
      decide
    · apply IsUnit.of_mul_eq_one (637 : ZMod 5059)
      decide
    · apply IsUnit.of_mul_eq_one (3905 : ZMod 5059)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_5077 : Nat.Prime 5077 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 5077 5076 1 2 [2, 2, 3, 3, 3, 47]
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
    · apply IsUnit.of_mul_eq_one (2538 : ZMod 5077)
      decide
    · apply IsUnit.of_mul_eq_one (2235 : ZMod 5077)
      decide
    · apply IsUnit.of_mul_eq_one (3509 : ZMod 5077)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_5081 : Nat.Prime 5081 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 5081 5080 1 3 [2, 2, 2, 5, 127]
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
    · apply IsUnit.of_mul_eq_one (2540 : ZMod 5081)
      decide
    · apply IsUnit.of_mul_eq_one (2336 : ZMod 5081)
      decide
    · apply IsUnit.of_mul_eq_one (2006 : ZMod 5081)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_5087 : Nat.Prime 5087 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 5087 5086 1 5 [2, 2543]
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
    · apply IsUnit.of_mul_eq_one (2543 : ZMod 5087)
      decide
    · apply IsUnit.of_mul_eq_one (212 : ZMod 5087)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_5099 : Nat.Prime 5099 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 5099 5098 1 2 [2, 2549]
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
    · apply IsUnit.of_mul_eq_one (2549 : ZMod 5099)
      decide
    · apply IsUnit.of_mul_eq_one (1700 : ZMod 5099)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_5101 : Nat.Prime 5101 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 5101 5100 1 6 [2, 2, 3, 5, 5, 17]
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
    · apply IsUnit.of_mul_eq_one (2550 : ZMod 5101)
      decide
    · apply IsUnit.of_mul_eq_one (2238 : ZMod 5101)
      decide
    · apply IsUnit.of_mul_eq_one (4441 : ZMod 5101)
      decide
    · apply IsUnit.of_mul_eq_one (1688 : ZMod 5101)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_5107 : Nat.Prime 5107 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 5107 5106 1 2 [2, 3, 23, 37]
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
    · apply IsUnit.of_mul_eq_one (2553 : ZMod 5107)
      decide
    · apply IsUnit.of_mul_eq_one (3508 : ZMod 5107)
      decide
    · apply IsUnit.of_mul_eq_one (298 : ZMod 5107)
      decide
    · apply IsUnit.of_mul_eq_one (4488 : ZMod 5107)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_5113 : Nat.Prime 5113 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 5113 5112 1 19 [2, 2, 2, 3, 3, 71]
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
    · apply IsUnit.of_mul_eq_one (2556 : ZMod 5113)
      decide
    · apply IsUnit.of_mul_eq_one (3432 : ZMod 5113)
      decide
    · apply IsUnit.of_mul_eq_one (2372 : ZMod 5113)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_5119 : Nat.Prime 5119 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 5119 5118 1 3 [2, 3, 853]
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
    · apply IsUnit.of_mul_eq_one (2559 : ZMod 5119)
      decide
    · apply IsUnit.of_mul_eq_one (1145 : ZMod 5119)
      decide
    · apply IsUnit.of_mul_eq_one (4451 : ZMod 5119)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_5147 : Nat.Prime 5147 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 5147 5146 1 2 [2, 31, 83]
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
    · apply IsUnit.of_mul_eq_one (2573 : ZMod 5147)
      decide
    · apply IsUnit.of_mul_eq_one (1981 : ZMod 5147)
      decide
    · apply IsUnit.of_mul_eq_one (3958 : ZMod 5147)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_5153 : Nat.Prime 5153 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 5153 5152 1 5 [2, 2, 2, 2, 2, 7, 23]
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
    · apply IsUnit.of_mul_eq_one (2576 : ZMod 5153)
      decide
    · apply IsUnit.of_mul_eq_one (1229 : ZMod 5153)
      decide
    · apply IsUnit.of_mul_eq_one (3674 : ZMod 5153)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_5167 : Nat.Prime 5167 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 5167 5166 1 6 [2, 3, 3, 7, 41]
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
    · apply IsUnit.of_mul_eq_one (2583 : ZMod 5167)
      decide
    · apply IsUnit.of_mul_eq_one (41 : ZMod 5167)
      decide
    · apply IsUnit.of_mul_eq_one (3224 : ZMod 5167)
      decide
    · apply IsUnit.of_mul_eq_one (1956 : ZMod 5167)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_5171 : Nat.Prime 5171 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 5171 5170 1 2 [2, 5, 11, 47]
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
    · apply IsUnit.of_mul_eq_one (2585 : ZMod 5171)
      decide
    · apply IsUnit.of_mul_eq_one (3852 : ZMod 5171)
      decide
    · apply IsUnit.of_mul_eq_one (3760 : ZMod 5171)
      decide
    · apply IsUnit.of_mul_eq_one (2992 : ZMod 5171)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_5179 : Nat.Prime 5179 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 5179 5178 1 2 [2, 3, 863]
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
    · apply IsUnit.of_mul_eq_one (2589 : ZMod 5179)
      decide
    · apply IsUnit.of_mul_eq_one (2953 : ZMod 5179)
      decide
    · apply IsUnit.of_mul_eq_one (2384 : ZMod 5179)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_5189 : Nat.Prime 5189 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 5189 5188 1 2 [2, 2, 1297]
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
    · apply IsUnit.of_mul_eq_one (2594 : ZMod 5189)
      decide
    · apply IsUnit.of_mul_eq_one (346 : ZMod 5189)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_5197 : Nat.Prime 5197 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 5197 5196 1 7 [2, 2, 3, 433]
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
    · apply IsUnit.of_mul_eq_one (2598 : ZMod 5197)
      decide
    · apply IsUnit.of_mul_eq_one (2838 : ZMod 5197)
      decide
    · apply IsUnit.of_mul_eq_one (1148 : ZMod 5197)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_5209 : Nat.Prime 5209 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 5209 5208 1 17 [2, 2, 2, 3, 7, 31]
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
    · apply IsUnit.of_mul_eq_one (2604 : ZMod 5209)
      decide
    · apply IsUnit.of_mul_eq_one (397 : ZMod 5209)
      decide
    · apply IsUnit.of_mul_eq_one (1458 : ZMod 5209)
      decide
    · apply IsUnit.of_mul_eq_one (4692 : ZMod 5209)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_5227 : Nat.Prime 5227 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 5227 5226 1 2 [2, 3, 13, 67]
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
    · apply IsUnit.of_mul_eq_one (2613 : ZMod 5227)
      decide
    · apply IsUnit.of_mul_eq_one (5076 : ZMod 5227)
      decide
    · apply IsUnit.of_mul_eq_one (917 : ZMod 5227)
      decide
    · apply IsUnit.of_mul_eq_one (5132 : ZMod 5227)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_5231 : Nat.Prime 5231 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 5231 5230 1 7 [2, 5, 523]
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
    · apply IsUnit.of_mul_eq_one (2615 : ZMod 5231)
      decide
    · apply IsUnit.of_mul_eq_one (2848 : ZMod 5231)
      decide
    · apply IsUnit.of_mul_eq_one (5034 : ZMod 5231)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_5233 : Nat.Prime 5233 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 5233 5232 1 10 [2, 2, 2, 2, 3, 109]
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
    · apply IsUnit.of_mul_eq_one (2616 : ZMod 5233)
      decide
    · apply IsUnit.of_mul_eq_one (110 : ZMod 5233)
      decide
    · apply IsUnit.of_mul_eq_one (1956 : ZMod 5233)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_5237 : Nat.Prime 5237 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 5237 5236 1 3 [2, 2, 7, 11, 17]
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
    · apply IsUnit.of_mul_eq_one (2618 : ZMod 5237)
      decide
    · apply IsUnit.of_mul_eq_one (276 : ZMod 5237)
      decide
    · apply IsUnit.of_mul_eq_one (1799 : ZMod 5237)
      decide
    · apply IsUnit.of_mul_eq_one (2657 : ZMod 5237)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_5261 : Nat.Prime 5261 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 5261 5260 1 2 [2, 2, 5, 263]
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
    · apply IsUnit.of_mul_eq_one (2630 : ZMod 5261)
      decide
    · apply IsUnit.of_mul_eq_one (3505 : ZMod 5261)
      decide
    · apply IsUnit.of_mul_eq_one (4486 : ZMod 5261)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_5273 : Nat.Prime 5273 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 5273 5272 1 3 [2, 2, 2, 659]
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
    · apply IsUnit.of_mul_eq_one (2636 : ZMod 5273)
      decide
    · apply IsUnit.of_mul_eq_one (4134 : ZMod 5273)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_5279 : Nat.Prime 5279 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 5279 5278 1 7 [2, 7, 13, 29]
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
    · apply IsUnit.of_mul_eq_one (2639 : ZMod 5279)
      decide
    · apply IsUnit.of_mul_eq_one (2097 : ZMod 5279)
      decide
    · apply IsUnit.of_mul_eq_one (5198 : ZMod 5279)
      decide
    · apply IsUnit.of_mul_eq_one (1625 : ZMod 5279)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_5281 : Nat.Prime 5281 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 5281 5280 1 7 [2, 2, 2, 2, 2, 3, 5, 11]
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
    · apply IsUnit.of_mul_eq_one (2640 : ZMod 5281)
      decide
    · apply IsUnit.of_mul_eq_one (1292 : ZMod 5281)
      decide
    · apply IsUnit.of_mul_eq_one (1696 : ZMod 5281)
      decide
    · apply IsUnit.of_mul_eq_one (4317 : ZMod 5281)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_5297 : Nat.Prime 5297 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 5297 5296 1 3 [2, 2, 2, 2, 331]
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
    · apply IsUnit.of_mul_eq_one (2648 : ZMod 5297)
      decide
    · apply IsUnit.of_mul_eq_one (3776 : ZMod 5297)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_5303 : Nat.Prime 5303 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 5303 5302 1 5 [2, 11, 241]
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
    · apply IsUnit.of_mul_eq_one (2651 : ZMod 5303)
      decide
    · apply IsUnit.of_mul_eq_one (1881 : ZMod 5303)
      decide
    · apply IsUnit.of_mul_eq_one (5071 : ZMod 5303)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_5309 : Nat.Prime 5309 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 5309 5308 1 2 [2, 2, 1327]
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
    · apply IsUnit.of_mul_eq_one (2654 : ZMod 5309)
      decide
    · apply IsUnit.of_mul_eq_one (354 : ZMod 5309)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_5323 : Nat.Prime 5323 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 5323 5322 1 5 [2, 3, 887]
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
    · apply IsUnit.of_mul_eq_one (2661 : ZMod 5323)
      decide
    · apply IsUnit.of_mul_eq_one (4895 : ZMod 5323)
      decide
    · apply IsUnit.of_mul_eq_one (108 : ZMod 5323)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_5333 : Nat.Prime 5333 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 5333 5332 1 2 [2, 2, 31, 43]
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
    · apply IsUnit.of_mul_eq_one (2666 : ZMod 5333)
      decide
    · apply IsUnit.of_mul_eq_one (2862 : ZMod 5333)
      decide
    · apply IsUnit.of_mul_eq_one (587 : ZMod 5333)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_5347 : Nat.Prime 5347 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 5347 5346 1 3 [2, 3, 3, 3, 3, 3, 11]
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
    · apply IsUnit.of_mul_eq_one (2673 : ZMod 5347)
      decide
    · apply IsUnit.of_mul_eq_one (3724 : ZMod 5347)
      decide
    · apply IsUnit.of_mul_eq_one (1863 : ZMod 5347)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_5351 : Nat.Prime 5351 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 5351 5350 1 11 [2, 5, 5, 107]
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
    · apply IsUnit.of_mul_eq_one (2675 : ZMod 5351)
      decide
    · apply IsUnit.of_mul_eq_one (840 : ZMod 5351)
      decide
    · apply IsUnit.of_mul_eq_one (2396 : ZMod 5351)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_5381 : Nat.Prime 5381 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 5381 5380 1 3 [2, 2, 5, 269]
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
    · apply IsUnit.of_mul_eq_one (2690 : ZMod 5381)
      decide
    · apply IsUnit.of_mul_eq_one (5247 : ZMod 5381)
      decide
    · apply IsUnit.of_mul_eq_one (427 : ZMod 5381)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_5387 : Nat.Prime 5387 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 5387 5386 1 2 [2, 2693]
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
    · apply IsUnit.of_mul_eq_one (2693 : ZMod 5387)
      decide
    · apply IsUnit.of_mul_eq_one (1796 : ZMod 5387)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_5393 : Nat.Prime 5393 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 5393 5392 1 3 [2, 2, 2, 2, 337]
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
    · apply IsUnit.of_mul_eq_one (2696 : ZMod 5393)
      decide
    · apply IsUnit.of_mul_eq_one (1021 : ZMod 5393)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_5399 : Nat.Prime 5399 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 5399 5398 1 7 [2, 2699]
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
    · apply IsUnit.of_mul_eq_one (2699 : ZMod 5399)
      decide
    · apply IsUnit.of_mul_eq_one (2812 : ZMod 5399)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_5407 : Nat.Prime 5407 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 5407 5406 1 3 [2, 3, 17, 53]
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
    · apply IsUnit.of_mul_eq_one (2703 : ZMod 5407)
      decide
    · apply IsUnit.of_mul_eq_one (347 : ZMod 5407)
      decide
    · apply IsUnit.of_mul_eq_one (4925 : ZMod 5407)
      decide
    · apply IsUnit.of_mul_eq_one (4042 : ZMod 5407)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_5413 : Nat.Prime 5413 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 5413 5412 1 5 [2, 2, 3, 11, 41]
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
    · apply IsUnit.of_mul_eq_one (2706 : ZMod 5413)
      decide
    · apply IsUnit.of_mul_eq_one (3200 : ZMod 5413)
      decide
    · apply IsUnit.of_mul_eq_one (5066 : ZMod 5413)
      decide
    · apply IsUnit.of_mul_eq_one (1957 : ZMod 5413)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_5417 : Nat.Prime 5417 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 5417 5416 1 3 [2, 2, 2, 677]
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
    · apply IsUnit.of_mul_eq_one (2708 : ZMod 5417)
      decide
    · apply IsUnit.of_mul_eq_one (1327 : ZMod 5417)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_5419 : Nat.Prime 5419 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 5419 5418 1 3 [2, 3, 3, 7, 43]
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
    · apply IsUnit.of_mul_eq_one (2709 : ZMod 5419)
      decide
    · apply IsUnit.of_mul_eq_one (42 : ZMod 5419)
      decide
    · apply IsUnit.of_mul_eq_one (5333 : ZMod 5419)
      decide
    · apply IsUnit.of_mul_eq_one (4270 : ZMod 5419)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_5431 : Nat.Prime 5431 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 5431 5430 1 3 [2, 3, 5, 181]
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
    · apply IsUnit.of_mul_eq_one (2715 : ZMod 5431)
      decide
    · apply IsUnit.of_mul_eq_one (2321 : ZMod 5431)
      decide
    · apply IsUnit.of_mul_eq_one (429 : ZMod 5431)
      decide
    · apply IsUnit.of_mul_eq_one (3566 : ZMod 5431)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_5437 : Nat.Prime 5437 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 5437 5436 1 5 [2, 2, 3, 3, 151]
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
    · apply IsUnit.of_mul_eq_one (2718 : ZMod 5437)
      decide
    · apply IsUnit.of_mul_eq_one (2867 : ZMod 5437)
      decide
    · apply IsUnit.of_mul_eq_one (3113 : ZMod 5437)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_5441 : Nat.Prime 5441 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 5441 5440 1 3 [2, 2, 2, 2, 2, 2, 5, 17]
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
    · apply IsUnit.of_mul_eq_one (2720 : ZMod 5441)
      decide
    · apply IsUnit.of_mul_eq_one (2168 : ZMod 5441)
      decide
    · apply IsUnit.of_mul_eq_one (4226 : ZMod 5441)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_5443 : Nat.Prime 5443 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 5443 5442 1 2 [2, 3, 907]
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
    · apply IsUnit.of_mul_eq_one (2721 : ZMod 5443)
      decide
    · apply IsUnit.of_mul_eq_one (951 : ZMod 5443)
      decide
    · apply IsUnit.of_mul_eq_one (432 : ZMod 5443)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_5449 : Nat.Prime 5449 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 5449 5448 1 7 [2, 2, 2, 3, 227]
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
    · apply IsUnit.of_mul_eq_one (2724 : ZMod 5449)
      decide
    · apply IsUnit.of_mul_eq_one (491 : ZMod 5449)
      decide
    · apply IsUnit.of_mul_eq_one (3591 : ZMod 5449)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_5471 : Nat.Prime 5471 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 5471 5470 1 7 [2, 5, 547]
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
    · apply IsUnit.of_mul_eq_one (2735 : ZMod 5471)
      decide
    · apply IsUnit.of_mul_eq_one (285 : ZMod 5471)
      decide
    · apply IsUnit.of_mul_eq_one (4140 : ZMod 5471)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_5477 : Nat.Prime 5477 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 5477 5476 1 2 [2, 2, 37, 37]
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
    · apply IsUnit.of_mul_eq_one (2738 : ZMod 5477)
      decide
    · apply IsUnit.of_mul_eq_one (4911 : ZMod 5477)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_5479 : Nat.Prime 5479 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 5479 5478 1 3 [2, 3, 11, 83]
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
    · apply IsUnit.of_mul_eq_one (2739 : ZMod 5479)
      decide
    · apply IsUnit.of_mul_eq_one (925 : ZMod 5479)
      decide
    · apply IsUnit.of_mul_eq_one (3119 : ZMod 5479)
      decide
    · apply IsUnit.of_mul_eq_one (4626 : ZMod 5479)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_5483 : Nat.Prime 5483 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 5483 5482 1 2 [2, 2741]
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
    · apply IsUnit.of_mul_eq_one (2741 : ZMod 5483)
      decide
    · apply IsUnit.of_mul_eq_one (1828 : ZMod 5483)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_5501 : Nat.Prime 5501 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 5501 5500 1 2 [2, 2, 5, 5, 5, 11]
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
    · apply IsUnit.of_mul_eq_one (2750 : ZMod 5501)
      decide
    · apply IsUnit.of_mul_eq_one (1127 : ZMod 5501)
      decide
    · apply IsUnit.of_mul_eq_one (2645 : ZMod 5501)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
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
  · decide
  · intro q hq
    simp at hq
    rcases hq with rfl | rfl | rfl | rfl
    · apply IsUnit.of_mul_eq_one (2751 : ZMod 5503)
      decide
    · apply IsUnit.of_mul_eq_one (3978 : ZMod 5503)
      decide
    · apply IsUnit.of_mul_eq_one (4163 : ZMod 5503)
      decide
    · apply IsUnit.of_mul_eq_one (2529 : ZMod 5503)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
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
  · decide
  · intro q hq
    simp at hq
    rcases hq with rfl | rfl
    · apply IsUnit.of_mul_eq_one (2753 : ZMod 5507)
      decide
    · apply IsUnit.of_mul_eq_one (1836 : ZMod 5507)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
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
  · decide
  · intro q hq
    simp at hq
    rcases hq with rfl | rfl | rfl
    · apply IsUnit.of_mul_eq_one (2759 : ZMod 5519)
      decide
    · apply IsUnit.of_mul_eq_one (2745 : ZMod 5519)
      decide
    · apply IsUnit.of_mul_eq_one (943 : ZMod 5519)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
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
  · decide
  · intro q hq
    simp at hq
    rcases hq with rfl | rfl | rfl | rfl
    · apply IsUnit.of_mul_eq_one (2760 : ZMod 5521)
      decide
    · apply IsUnit.of_mul_eq_one (113 : ZMod 5521)
      decide
    · apply IsUnit.of_mul_eq_one (571 : ZMod 5521)
      decide
    · apply IsUnit.of_mul_eq_one (2270 : ZMod 5521)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
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
  · decide
  · intro q hq
    simp at hq
    rcases hq with rfl | rfl | rfl
    · apply IsUnit.of_mul_eq_one (2763 : ZMod 5527)
      decide
    · apply IsUnit.of_mul_eq_one (3392 : ZMod 5527)
      decide
    · apply IsUnit.of_mul_eq_one (4760 : ZMod 5527)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
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
  · decide
  · intro q hq
    simp at hq
    rcases hq with rfl | rfl | rfl | rfl
    · apply IsUnit.of_mul_eq_one (2765 : ZMod 5531)
      decide
    · apply IsUnit.of_mul_eq_one (2080 : ZMod 5531)
      decide
    · apply IsUnit.of_mul_eq_one (2446 : ZMod 5531)
      decide
    · apply IsUnit.of_mul_eq_one (733 : ZMod 5531)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
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
  · decide
  · intro q hq
    simp at hq
    rcases hq with rfl | rfl | rfl
    · apply IsUnit.of_mul_eq_one (2778 : ZMod 5557)
      decide
    · apply IsUnit.of_mul_eq_one (3095 : ZMod 5557)
      decide
    · apply IsUnit.of_mul_eq_one (3972 : ZMod 5557)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
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
  · decide
  · intro q hq
    simp at hq
    rcases hq with rfl | rfl | rfl
    · apply IsUnit.of_mul_eq_one (2781 : ZMod 5563)
      decide
    · apply IsUnit.of_mul_eq_one (3471 : ZMod 5563)
      decide
    · apply IsUnit.of_mul_eq_one (5473 : ZMod 5563)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_5569 : Nat.Prime 5569 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 5569 5568 1 13 [2, 2, 2, 2, 2, 2, 3, 29]
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
    · apply IsUnit.of_mul_eq_one (2784 : ZMod 5569)
      decide
    · apply IsUnit.of_mul_eq_one (4821 : ZMod 5569)
      decide
    · apply IsUnit.of_mul_eq_one (996 : ZMod 5569)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_5573 : Nat.Prime 5573 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 5573 5572 1 2 [2, 2, 7, 199]
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
    · apply IsUnit.of_mul_eq_one (2786 : ZMod 5573)
      decide
    · apply IsUnit.of_mul_eq_one (388 : ZMod 5573)
      decide
    · apply IsUnit.of_mul_eq_one (3319 : ZMod 5573)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_5581 : Nat.Prime 5581 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 5581 5580 1 6 [2, 2, 3, 3, 5, 31]
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
    · apply IsUnit.of_mul_eq_one (2790 : ZMod 5581)
      decide
    · apply IsUnit.of_mul_eq_one (4761 : ZMod 5581)
      decide
    · apply IsUnit.of_mul_eq_one (3507 : ZMod 5581)
      decide
    · apply IsUnit.of_mul_eq_one (2354 : ZMod 5581)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_5591 : Nat.Prime 5591 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 5591 5590 1 11 [2, 5, 13, 43]
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
    · apply IsUnit.of_mul_eq_one (2795 : ZMod 5591)
      decide
    · apply IsUnit.of_mul_eq_one (4696 : ZMod 5591)
      decide
    · apply IsUnit.of_mul_eq_one (3478 : ZMod 5591)
      decide
    · apply IsUnit.of_mul_eq_one (1124 : ZMod 5591)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_5623 : Nat.Prime 5623 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 5623 5622 1 5 [2, 3, 937]
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
    · apply IsUnit.of_mul_eq_one (2811 : ZMod 5623)
      decide
    · apply IsUnit.of_mul_eq_one (3077 : ZMod 5623)
      decide
    · apply IsUnit.of_mul_eq_one (2606 : ZMod 5623)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_5639 : Nat.Prime 5639 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 5639 5638 1 7 [2, 2819]
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
    · apply IsUnit.of_mul_eq_one (2819 : ZMod 5639)
      decide
    · apply IsUnit.of_mul_eq_one (2937 : ZMod 5639)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_5641 : Nat.Prime 5641 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 5641 5640 1 14 [2, 2, 2, 3, 5, 47]
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
    · apply IsUnit.of_mul_eq_one (2820 : ZMod 5641)
      decide
    · apply IsUnit.of_mul_eq_one (681 : ZMod 5641)
      decide
    · apply IsUnit.of_mul_eq_one (4332 : ZMod 5641)
      decide
    · apply IsUnit.of_mul_eq_one (977 : ZMod 5641)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_5647 : Nat.Prime 5647 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 5647 5646 1 3 [2, 3, 941]
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
    · apply IsUnit.of_mul_eq_one (2823 : ZMod 5647)
      decide
    · apply IsUnit.of_mul_eq_one (5362 : ZMod 5647)
      decide
    · apply IsUnit.of_mul_eq_one (3669 : ZMod 5647)
      decide
  · norm_num
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_4673_4918_part03 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_4914 (p := 4813) (q := 4817) (by exact lowPrime_4817) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_4914 (p := 4817) (q := 4831) (by exact lowPrime_4831) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_4914 (p := 4831) (q := 4861) (by exact lowPrime_4861) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_4914 (p := 4861) (q := 4871) (by exact lowPrime_4871) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_4914 (p := 4871) (q := 4877) (by exact lowPrime_4877) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_4914 (p := 4877) (q := 4889) (by exact lowPrime_4889) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_4914 (p := 4889) (q := 4903) (by exact lowPrime_4903) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_4914 (p := 4903) (q := 4909) (by exact lowPrime_4909) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_4673_4918_part03_chain :
    DusartPrimeRowsChain 4813 4908 dusartPrimeRows_4673_4918_part03 := by
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
                  norm_num [dusartPrimeRow_of_explicit_4914, dusartPrimeRow_of_explicit_right]

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_4673_4918_part04 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_4914 (p := 4909) (q := 4919) (by exact lowPrime_4919) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_4673_4918_part04_chain :
    DusartPrimeRowsChain 4909 4918 dusartPrimeRows_4673_4918_part04 := by
  apply DusartPrimeRowsChain.cons
  · norm_num [dusartPrimeRow_of_explicit_4914]
  · norm_num [dusartPrimeRow_of_explicit_4914]
  · apply DusartPrimeRowsChain.empty
    norm_num [dusartPrimeRow_of_explicit_4914, dusartPrimeRow_of_explicit_right]

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_4919_5166_part01 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_5166 (p := 4919) (q := 4931) (by exact lowPrime_4931) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_5166 (p := 4931) (q := 4933) (by exact lowPrime_4933) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_5166 (p := 4933) (q := 4937) (by exact lowPrime_4937) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_5166 (p := 4937) (q := 4943) (by exact lowPrime_4943) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_5166 (p := 4943) (q := 4951) (by exact lowPrime_4951) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_5166 (p := 4951) (q := 4957) (by exact lowPrime_4957) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_5166 (p := 4957) (q := 4967) (by exact lowPrime_4967) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_5166 (p := 4967) (q := 4969) (by exact lowPrime_4969) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_4919_5166_part01_chain :
    DusartPrimeRowsChain 4919 4968 dusartPrimeRows_4919_5166_part01 := by
  apply DusartPrimeRowsChain.cons
  · norm_num [dusartPrimeRow_of_explicit_5166]
  · norm_num [dusartPrimeRow_of_explicit_5166]
  · apply DusartPrimeRowsChain.cons
    · norm_num [dusartPrimeRow_of_explicit_5166]
    · norm_num [dusartPrimeRow_of_explicit_5166]
    · apply DusartPrimeRowsChain.cons
      · norm_num [dusartPrimeRow_of_explicit_5166]
      · norm_num [dusartPrimeRow_of_explicit_5166]
      · apply DusartPrimeRowsChain.cons
        · norm_num [dusartPrimeRow_of_explicit_5166]
        · norm_num [dusartPrimeRow_of_explicit_5166]
        · apply DusartPrimeRowsChain.cons
          · norm_num [dusartPrimeRow_of_explicit_5166]
          · norm_num [dusartPrimeRow_of_explicit_5166]
          · apply DusartPrimeRowsChain.cons
            · norm_num [dusartPrimeRow_of_explicit_5166]
            · norm_num [dusartPrimeRow_of_explicit_5166]
            · apply DusartPrimeRowsChain.cons
              · norm_num [dusartPrimeRow_of_explicit_5166]
              · norm_num [dusartPrimeRow_of_explicit_5166]
              · apply DusartPrimeRowsChain.cons
                · norm_num [dusartPrimeRow_of_explicit_5166]
                · norm_num [dusartPrimeRow_of_explicit_5166]
                · apply DusartPrimeRowsChain.empty
                  norm_num [dusartPrimeRow_of_explicit_5166, dusartPrimeRow_of_explicit_right]

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_4919_5166_part02 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_5166 (p := 4969) (q := 4973) (by exact lowPrime_4973) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_5166 (p := 4973) (q := 4987) (by exact lowPrime_4987) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_5166 (p := 4987) (q := 4993) (by exact lowPrime_4993) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_5166 (p := 4993) (q := 4999) (by exact lowPrime_4999) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_5166 (p := 4999) (q := 5003) (by exact lowPrime_5003) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_5166 (p := 5003) (q := 5009) (by exact lowPrime_5009) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_5166 (p := 5009) (q := 5011) (by exact lowPrime_5011) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_5166 (p := 5011) (q := 5021) (by exact lowPrime_5021) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_4919_5166_part02_chain :
    DusartPrimeRowsChain 4969 5020 dusartPrimeRows_4919_5166_part02 := by
  apply DusartPrimeRowsChain.cons
  · norm_num [dusartPrimeRow_of_explicit_5166]
  · norm_num [dusartPrimeRow_of_explicit_5166]
  · apply DusartPrimeRowsChain.cons
    · norm_num [dusartPrimeRow_of_explicit_5166]
    · norm_num [dusartPrimeRow_of_explicit_5166]
    · apply DusartPrimeRowsChain.cons
      · norm_num [dusartPrimeRow_of_explicit_5166]
      · norm_num [dusartPrimeRow_of_explicit_5166]
      · apply DusartPrimeRowsChain.cons
        · norm_num [dusartPrimeRow_of_explicit_5166]
        · norm_num [dusartPrimeRow_of_explicit_5166]
        · apply DusartPrimeRowsChain.cons
          · norm_num [dusartPrimeRow_of_explicit_5166]
          · norm_num [dusartPrimeRow_of_explicit_5166]
          · apply DusartPrimeRowsChain.cons
            · norm_num [dusartPrimeRow_of_explicit_5166]
            · norm_num [dusartPrimeRow_of_explicit_5166]
            · apply DusartPrimeRowsChain.cons
              · norm_num [dusartPrimeRow_of_explicit_5166]
              · norm_num [dusartPrimeRow_of_explicit_5166]
              · apply DusartPrimeRowsChain.cons
                · norm_num [dusartPrimeRow_of_explicit_5166]
                · norm_num [dusartPrimeRow_of_explicit_5166]
                · apply DusartPrimeRowsChain.empty
                  norm_num [dusartPrimeRow_of_explicit_5166, dusartPrimeRow_of_explicit_right]

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_4919_5166_part03 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_5166 (p := 5021) (q := 5023) (by exact lowPrime_5023) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_5166 (p := 5023) (q := 5039) (by exact lowPrime_5039) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_5166 (p := 5039) (q := 5051) (by exact lowPrime_5051) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_5166 (p := 5051) (q := 5059) (by exact lowPrime_5059) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_5166 (p := 5059) (q := 5077) (by exact lowPrime_5077) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_5166 (p := 5077) (q := 5081) (by exact lowPrime_5081) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_5166 (p := 5081) (q := 5087) (by exact lowPrime_5087) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_5166 (p := 5087) (q := 5099) (by exact lowPrime_5099) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_4919_5166_part03_chain :
    DusartPrimeRowsChain 5021 5098 dusartPrimeRows_4919_5166_part03 := by
  apply DusartPrimeRowsChain.cons
  · norm_num [dusartPrimeRow_of_explicit_5166]
  · norm_num [dusartPrimeRow_of_explicit_5166]
  · apply DusartPrimeRowsChain.cons
    · norm_num [dusartPrimeRow_of_explicit_5166]
    · norm_num [dusartPrimeRow_of_explicit_5166]
    · apply DusartPrimeRowsChain.cons
      · norm_num [dusartPrimeRow_of_explicit_5166]
      · norm_num [dusartPrimeRow_of_explicit_5166]
      · apply DusartPrimeRowsChain.cons
        · norm_num [dusartPrimeRow_of_explicit_5166]
        · norm_num [dusartPrimeRow_of_explicit_5166]
        · apply DusartPrimeRowsChain.cons
          · norm_num [dusartPrimeRow_of_explicit_5166]
          · norm_num [dusartPrimeRow_of_explicit_5166]
          · apply DusartPrimeRowsChain.cons
            · norm_num [dusartPrimeRow_of_explicit_5166]
            · norm_num [dusartPrimeRow_of_explicit_5166]
            · apply DusartPrimeRowsChain.cons
              · norm_num [dusartPrimeRow_of_explicit_5166]
              · norm_num [dusartPrimeRow_of_explicit_5166]
              · apply DusartPrimeRowsChain.cons
                · norm_num [dusartPrimeRow_of_explicit_5166]
                · norm_num [dusartPrimeRow_of_explicit_5166]
                · apply DusartPrimeRowsChain.empty
                  norm_num [dusartPrimeRow_of_explicit_5166, dusartPrimeRow_of_explicit_right]

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_4919_5166_part04 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_5166 (p := 5099) (q := 5101) (by exact lowPrime_5101) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_5166 (p := 5101) (q := 5107) (by exact lowPrime_5107) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_5166 (p := 5107) (q := 5113) (by exact lowPrime_5113) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_5166 (p := 5113) (q := 5119) (by exact lowPrime_5119) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_5166 (p := 5119) (q := 5147) (by exact lowPrime_5147) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_5166 (p := 5147) (q := 5153) (by exact lowPrime_5153) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_5166 (p := 5153) (q := 5167) (by exact lowPrime_5167) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_4919_5166_part04_chain :
    DusartPrimeRowsChain 5099 5166 dusartPrimeRows_4919_5166_part04 := by
  apply DusartPrimeRowsChain.cons
  · norm_num [dusartPrimeRow_of_explicit_5166]
  · norm_num [dusartPrimeRow_of_explicit_5166]
  · apply DusartPrimeRowsChain.cons
    · norm_num [dusartPrimeRow_of_explicit_5166]
    · norm_num [dusartPrimeRow_of_explicit_5166]
    · apply DusartPrimeRowsChain.cons
      · norm_num [dusartPrimeRow_of_explicit_5166]
      · norm_num [dusartPrimeRow_of_explicit_5166]
      · apply DusartPrimeRowsChain.cons
        · norm_num [dusartPrimeRow_of_explicit_5166]
        · norm_num [dusartPrimeRow_of_explicit_5166]
        · apply DusartPrimeRowsChain.cons
          · norm_num [dusartPrimeRow_of_explicit_5166]
          · norm_num [dusartPrimeRow_of_explicit_5166]
          · apply DusartPrimeRowsChain.cons
            · norm_num [dusartPrimeRow_of_explicit_5166]
            · norm_num [dusartPrimeRow_of_explicit_5166]
            · apply DusartPrimeRowsChain.cons
              · norm_num [dusartPrimeRow_of_explicit_5166]
              · norm_num [dusartPrimeRow_of_explicit_5166]
              · apply DusartPrimeRowsChain.empty
                norm_num [dusartPrimeRow_of_explicit_5166, dusartPrimeRow_of_explicit_right]

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_5167_5436_part01 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_5431 (p := 5167) (q := 5171) (by exact lowPrime_5171) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_5431 (p := 5171) (q := 5179) (by exact lowPrime_5179) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_5431 (p := 5179) (q := 5189) (by exact lowPrime_5189) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_5431 (p := 5189) (q := 5197) (by exact lowPrime_5197) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_5431 (p := 5197) (q := 5209) (by exact lowPrime_5209) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_5431 (p := 5209) (q := 5227) (by exact lowPrime_5227) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_5431 (p := 5227) (q := 5231) (by exact lowPrime_5231) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_5431 (p := 5231) (q := 5233) (by exact lowPrime_5233) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_5167_5436_part01_chain :
    DusartPrimeRowsChain 5167 5232 dusartPrimeRows_5167_5436_part01 := by
  apply DusartPrimeRowsChain.cons
  · norm_num [dusartPrimeRow_of_explicit_5431]
  · norm_num [dusartPrimeRow_of_explicit_5431]
  · apply DusartPrimeRowsChain.cons
    · norm_num [dusartPrimeRow_of_explicit_5431]
    · norm_num [dusartPrimeRow_of_explicit_5431]
    · apply DusartPrimeRowsChain.cons
      · norm_num [dusartPrimeRow_of_explicit_5431]
      · norm_num [dusartPrimeRow_of_explicit_5431]
      · apply DusartPrimeRowsChain.cons
        · norm_num [dusartPrimeRow_of_explicit_5431]
        · norm_num [dusartPrimeRow_of_explicit_5431]
        · apply DusartPrimeRowsChain.cons
          · norm_num [dusartPrimeRow_of_explicit_5431]
          · norm_num [dusartPrimeRow_of_explicit_5431]
          · apply DusartPrimeRowsChain.cons
            · norm_num [dusartPrimeRow_of_explicit_5431]
            · norm_num [dusartPrimeRow_of_explicit_5431]
            · apply DusartPrimeRowsChain.cons
              · norm_num [dusartPrimeRow_of_explicit_5431]
              · norm_num [dusartPrimeRow_of_explicit_5431]
              · apply DusartPrimeRowsChain.cons
                · norm_num [dusartPrimeRow_of_explicit_5431]
                · norm_num [dusartPrimeRow_of_explicit_5431]
                · apply DusartPrimeRowsChain.empty
                  norm_num [dusartPrimeRow_of_explicit_5431, dusartPrimeRow_of_explicit_right]

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_5167_5436_part02 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_5431 (p := 5233) (q := 5237) (by exact lowPrime_5237) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_5431 (p := 5237) (q := 5261) (by exact lowPrime_5261) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_5431 (p := 5261) (q := 5273) (by exact lowPrime_5273) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_5431 (p := 5273) (q := 5279) (by exact lowPrime_5279) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_5431 (p := 5279) (q := 5281) (by exact lowPrime_5281) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_5431 (p := 5281) (q := 5297) (by exact lowPrime_5297) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_5431 (p := 5297) (q := 5303) (by exact lowPrime_5303) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_5431 (p := 5303) (q := 5309) (by exact lowPrime_5309) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_5167_5436_part02_chain :
    DusartPrimeRowsChain 5233 5308 dusartPrimeRows_5167_5436_part02 := by
  apply DusartPrimeRowsChain.cons
  · norm_num [dusartPrimeRow_of_explicit_5431]
  · norm_num [dusartPrimeRow_of_explicit_5431]
  · apply DusartPrimeRowsChain.cons
    · norm_num [dusartPrimeRow_of_explicit_5431]
    · norm_num [dusartPrimeRow_of_explicit_5431]
    · apply DusartPrimeRowsChain.cons
      · norm_num [dusartPrimeRow_of_explicit_5431]
      · norm_num [dusartPrimeRow_of_explicit_5431]
      · apply DusartPrimeRowsChain.cons
        · norm_num [dusartPrimeRow_of_explicit_5431]
        · norm_num [dusartPrimeRow_of_explicit_5431]
        · apply DusartPrimeRowsChain.cons
          · norm_num [dusartPrimeRow_of_explicit_5431]
          · norm_num [dusartPrimeRow_of_explicit_5431]
          · apply DusartPrimeRowsChain.cons
            · norm_num [dusartPrimeRow_of_explicit_5431]
            · norm_num [dusartPrimeRow_of_explicit_5431]
            · apply DusartPrimeRowsChain.cons
              · norm_num [dusartPrimeRow_of_explicit_5431]
              · norm_num [dusartPrimeRow_of_explicit_5431]
              · apply DusartPrimeRowsChain.cons
                · norm_num [dusartPrimeRow_of_explicit_5431]
                · norm_num [dusartPrimeRow_of_explicit_5431]
                · apply DusartPrimeRowsChain.empty
                  norm_num [dusartPrimeRow_of_explicit_5431, dusartPrimeRow_of_explicit_right]

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_5167_5436_part03 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_5431 (p := 5309) (q := 5323) (by exact lowPrime_5323) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_5431 (p := 5323) (q := 5333) (by exact lowPrime_5333) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_5431 (p := 5333) (q := 5347) (by exact lowPrime_5347) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_5431 (p := 5347) (q := 5351) (by exact lowPrime_5351) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_5431 (p := 5351) (q := 5381) (by exact lowPrime_5381) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_5431 (p := 5381) (q := 5387) (by exact lowPrime_5387) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_5431 (p := 5387) (q := 5393) (by exact lowPrime_5393) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_5431 (p := 5393) (q := 5399) (by exact lowPrime_5399) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_5167_5436_part03_chain :
    DusartPrimeRowsChain 5309 5398 dusartPrimeRows_5167_5436_part03 := by
  apply DusartPrimeRowsChain.cons
  · norm_num [dusartPrimeRow_of_explicit_5431]
  · norm_num [dusartPrimeRow_of_explicit_5431]
  · apply DusartPrimeRowsChain.cons
    · norm_num [dusartPrimeRow_of_explicit_5431]
    · norm_num [dusartPrimeRow_of_explicit_5431]
    · apply DusartPrimeRowsChain.cons
      · norm_num [dusartPrimeRow_of_explicit_5431]
      · norm_num [dusartPrimeRow_of_explicit_5431]
      · apply DusartPrimeRowsChain.cons
        · norm_num [dusartPrimeRow_of_explicit_5431]
        · norm_num [dusartPrimeRow_of_explicit_5431]
        · apply DusartPrimeRowsChain.cons
          · norm_num [dusartPrimeRow_of_explicit_5431]
          · norm_num [dusartPrimeRow_of_explicit_5431]
          · apply DusartPrimeRowsChain.cons
            · norm_num [dusartPrimeRow_of_explicit_5431]
            · norm_num [dusartPrimeRow_of_explicit_5431]
            · apply DusartPrimeRowsChain.cons
              · norm_num [dusartPrimeRow_of_explicit_5431]
              · norm_num [dusartPrimeRow_of_explicit_5431]
              · apply DusartPrimeRowsChain.cons
                · norm_num [dusartPrimeRow_of_explicit_5431]
                · norm_num [dusartPrimeRow_of_explicit_5431]
                · apply DusartPrimeRowsChain.empty
                  norm_num [dusartPrimeRow_of_explicit_5431, dusartPrimeRow_of_explicit_right]

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_5167_5436_part04 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_5431 (p := 5399) (q := 5407) (by exact lowPrime_5407) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_5431 (p := 5407) (q := 5413) (by exact lowPrime_5413) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_5431 (p := 5413) (q := 5417) (by exact lowPrime_5417) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_5431 (p := 5417) (q := 5419) (by exact lowPrime_5419) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_5431 (p := 5419) (q := 5431) (by exact lowPrime_5431) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_5431 (p := 5431) (q := 5437) (by exact lowPrime_5437) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_5167_5436_part04_chain :
    DusartPrimeRowsChain 5399 5436 dusartPrimeRows_5167_5436_part04 := by
  apply DusartPrimeRowsChain.cons
  · norm_num [dusartPrimeRow_of_explicit_5431]
  · norm_num [dusartPrimeRow_of_explicit_5431]
  · apply DusartPrimeRowsChain.cons
    · norm_num [dusartPrimeRow_of_explicit_5431]
    · norm_num [dusartPrimeRow_of_explicit_5431]
    · apply DusartPrimeRowsChain.cons
      · norm_num [dusartPrimeRow_of_explicit_5431]
      · norm_num [dusartPrimeRow_of_explicit_5431]
      · apply DusartPrimeRowsChain.cons
        · norm_num [dusartPrimeRow_of_explicit_5431]
        · norm_num [dusartPrimeRow_of_explicit_5431]
        · apply DusartPrimeRowsChain.cons
          · norm_num [dusartPrimeRow_of_explicit_5431]
          · norm_num [dusartPrimeRow_of_explicit_5431]
          · apply DusartPrimeRowsChain.cons
            · norm_num [dusartPrimeRow_of_explicit_5431]
            · norm_num [dusartPrimeRow_of_explicit_5431]
            · apply DusartPrimeRowsChain.empty
              norm_num [dusartPrimeRow_of_explicit_5431, dusartPrimeRow_of_explicit_right]

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_5437_5710_part01 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_5710 (p := 5437) (q := 5441) (by exact lowPrime_5441) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_5710 (p := 5441) (q := 5443) (by exact lowPrime_5443) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_5710 (p := 5443) (q := 5449) (by exact lowPrime_5449) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_5710 (p := 5449) (q := 5471) (by exact lowPrime_5471) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_5710 (p := 5471) (q := 5477) (by exact lowPrime_5477) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_5710 (p := 5477) (q := 5479) (by exact lowPrime_5479) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_5710 (p := 5479) (q := 5483) (by exact lowPrime_5483) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_5710 (p := 5483) (q := 5501) (by exact lowPrime_5501) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_5437_5710_part01_chain :
    DusartPrimeRowsChain 5437 5500 dusartPrimeRows_5437_5710_part01 := by
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
                  norm_num [dusartPrimeRow_of_explicit_5710, dusartPrimeRow_of_explicit_right]

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
    DusartPrimeRowsChain 5501 5562 dusartPrimeRows_5437_5710_part02 := by
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
                  norm_num [dusartPrimeRow_of_explicit_5710, dusartPrimeRow_of_explicit_right]

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_5437_5710_part03 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_5710 (p := 5563) (q := 5569) (by exact lowPrime_5569) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_5710 (p := 5569) (q := 5573) (by exact lowPrime_5573) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_5710 (p := 5573) (q := 5581) (by exact lowPrime_5581) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_5710 (p := 5581) (q := 5591) (by exact lowPrime_5591) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_5710 (p := 5591) (q := 5623) (by exact lowPrime_5623) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_5710 (p := 5623) (q := 5639) (by exact lowPrime_5639) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_5710 (p := 5639) (q := 5641) (by exact lowPrime_5641) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_5710 (p := 5641) (q := 5647) (by exact lowPrime_5647) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_5437_5710_part03_chain :
    DusartPrimeRowsChain 5563 5646 dusartPrimeRows_5437_5710_part03 := by
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
                  norm_num [dusartPrimeRow_of_explicit_5710, dusartPrimeRow_of_explicit_right]
