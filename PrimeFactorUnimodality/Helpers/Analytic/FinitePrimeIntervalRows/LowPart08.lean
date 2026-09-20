import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowBase

set_option autoImplicit false
set_option maxRecDepth 1000000

/-! # Lower finite Dusart prefix chunk 08 -/

namespace PrimeFactorUnimodality

noncomputable section
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_8969 : Nat.Prime 8969 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 8969 8968 1 3 [2, 2, 2, 19, 59]
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
    · apply IsUnit.of_mul_eq_one (4484 : ZMod 8969)
      decide
    · apply IsUnit.of_mul_eq_one (5749 : ZMod 8969)
      decide
    · apply IsUnit.of_mul_eq_one (5118 : ZMod 8969)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_8971 : Nat.Prime 8971 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 8971 8970 1 2 [2, 3, 5, 13, 23]
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
    · apply IsUnit.of_mul_eq_one (4485 : ZMod 8971)
      decide
    · apply IsUnit.of_mul_eq_one (6094 : ZMod 8971)
      decide
    · apply IsUnit.of_mul_eq_one (8016 : ZMod 8971)
      decide
    · apply IsUnit.of_mul_eq_one (3263 : ZMod 8971)
      decide
    · apply IsUnit.of_mul_eq_one (6727 : ZMod 8971)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_8999 : Nat.Prime 8999 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 8999 8998 1 7 [2, 11, 409]
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
    · apply IsUnit.of_mul_eq_one (4499 : ZMod 8999)
      decide
    · apply IsUnit.of_mul_eq_one (6640 : ZMod 8999)
      decide
    · apply IsUnit.of_mul_eq_one (1291 : ZMod 8999)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_9001 : Nat.Prime 9001 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 9001 9000 1 7 [2, 2, 2, 3, 3, 5, 5, 5]
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
    · apply IsUnit.of_mul_eq_one (4500 : ZMod 9001)
      decide
    · apply IsUnit.of_mul_eq_one (4266 : ZMod 9001)
      decide
    · apply IsUnit.of_mul_eq_one (4608 : ZMod 9001)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_9007 : Nat.Prime 9007 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 9007 9006 1 3 [2, 3, 19, 79]
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
    · apply IsUnit.of_mul_eq_one (4503 : ZMod 9007)
      decide
    · apply IsUnit.of_mul_eq_one (6369 : ZMod 9007)
      decide
    · apply IsUnit.of_mul_eq_one (5491 : ZMod 9007)
      decide
    · apply IsUnit.of_mul_eq_one (3381 : ZMod 9007)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_9011 : Nat.Prime 9011 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 9011 9010 1 2 [2, 5, 17, 53]
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
    · apply IsUnit.of_mul_eq_one (4505 : ZMod 9011)
      decide
    · apply IsUnit.of_mul_eq_one (4931 : ZMod 9011)
      decide
    · apply IsUnit.of_mul_eq_one (5686 : ZMod 9011)
      decide
    · apply IsUnit.of_mul_eq_one (7138 : ZMod 9011)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_9013 : Nat.Prime 9013 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 9013 9012 1 5 [2, 2, 3, 751]
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
    · apply IsUnit.of_mul_eq_one (4506 : ZMod 9013)
      decide
    · apply IsUnit.of_mul_eq_one (1108 : ZMod 9013)
      decide
    · apply IsUnit.of_mul_eq_one (402 : ZMod 9013)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_9029 : Nat.Prime 9029 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 9029 9028 1 2 [2, 2, 37, 61]
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
    · apply IsUnit.of_mul_eq_one (4514 : ZMod 9029)
      decide
    · apply IsUnit.of_mul_eq_one (1906 : ZMod 9029)
      decide
    · apply IsUnit.of_mul_eq_one (1880 : ZMod 9029)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_9041 : Nat.Prime 9041 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 9041 9040 1 3 [2, 2, 2, 2, 5, 113]
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
    · apply IsUnit.of_mul_eq_one (4520 : ZMod 9041)
      decide
    · apply IsUnit.of_mul_eq_one (6185 : ZMod 9041)
      decide
    · apply IsUnit.of_mul_eq_one (2530 : ZMod 9041)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_9043 : Nat.Prime 9043 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 9043 9042 1 3 [2, 3, 11, 137]
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
    · apply IsUnit.of_mul_eq_one (4521 : ZMod 9043)
      decide
    · apply IsUnit.of_mul_eq_one (7079 : ZMod 9043)
      decide
    · apply IsUnit.of_mul_eq_one (2545 : ZMod 9043)
      decide
    · apply IsUnit.of_mul_eq_one (4942 : ZMod 9043)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_9049 : Nat.Prime 9049 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 9049 9048 1 7 [2, 2, 2, 3, 13, 29]
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
    · apply IsUnit.of_mul_eq_one (4524 : ZMod 9049)
      decide
    · apply IsUnit.of_mul_eq_one (2734 : ZMod 9049)
      decide
    · apply IsUnit.of_mul_eq_one (8631 : ZMod 9049)
      decide
    · apply IsUnit.of_mul_eq_one (8210 : ZMod 9049)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_9059 : Nat.Prime 9059 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 9059 9058 1 2 [2, 7, 647]
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
    · apply IsUnit.of_mul_eq_one (4529 : ZMod 9059)
      decide
    · apply IsUnit.of_mul_eq_one (8032 : ZMod 9059)
      decide
    · apply IsUnit.of_mul_eq_one (3232 : ZMod 9059)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_9067 : Nat.Prime 9067 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 9067 9066 1 3 [2, 3, 1511]
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
    · apply IsUnit.of_mul_eq_one (4533 : ZMod 9067)
      decide
    · apply IsUnit.of_mul_eq_one (8706 : ZMod 9067)
      decide
    · apply IsUnit.of_mul_eq_one (8930 : ZMod 9067)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_9091 : Nat.Prime 9091 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 9091 9090 1 3 [2, 3, 3, 5, 101]
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
    · apply IsUnit.of_mul_eq_one (4545 : ZMod 9091)
      decide
    · apply IsUnit.of_mul_eq_one (1129 : ZMod 9091)
      decide
    · apply IsUnit.of_mul_eq_one (3214 : ZMod 9091)
      decide
    · apply IsUnit.of_mul_eq_one (5371 : ZMod 9091)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_9103 : Nat.Prime 9103 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 9103 9102 1 6 [2, 3, 37, 41]
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
    · apply IsUnit.of_mul_eq_one (4551 : ZMod 9103)
      decide
    · apply IsUnit.of_mul_eq_one (1574 : ZMod 9103)
      decide
    · apply IsUnit.of_mul_eq_one (8168 : ZMod 9103)
      decide
    · apply IsUnit.of_mul_eq_one (7338 : ZMod 9103)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_9109 : Nat.Prime 9109 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 9109 9108 1 10 [2, 2, 3, 3, 11, 23]
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
    · apply IsUnit.of_mul_eq_one (4554 : ZMod 9109)
      decide
    · apply IsUnit.of_mul_eq_one (5032 : ZMod 9109)
      decide
    · apply IsUnit.of_mul_eq_one (2742 : ZMod 9109)
      decide
    · apply IsUnit.of_mul_eq_one (975 : ZMod 9109)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_9127 : Nat.Prime 9127 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 9127 9126 1 3 [2, 3, 3, 3, 13, 13]
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
    · apply IsUnit.of_mul_eq_one (4563 : ZMod 9127)
      decide
    · apply IsUnit.of_mul_eq_one (8123 : ZMod 9127)
      decide
    · apply IsUnit.of_mul_eq_one (153 : ZMod 9127)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_9133 : Nat.Prime 9133 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 9133 9132 1 6 [2, 2, 3, 761]
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
    · apply IsUnit.of_mul_eq_one (4566 : ZMod 9133)
      decide
    · apply IsUnit.of_mul_eq_one (7354 : ZMod 9133)
      decide
    · apply IsUnit.of_mul_eq_one (7856 : ZMod 9133)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_9137 : Nat.Prime 9137 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 9137 9136 1 3 [2, 2, 2, 2, 571]
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
    · apply IsUnit.of_mul_eq_one (4568 : ZMod 9137)
      decide
    · apply IsUnit.of_mul_eq_one (4211 : ZMod 9137)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_9151 : Nat.Prime 9151 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 9151 9150 1 3 [2, 3, 5, 5, 61]
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
    · apply IsUnit.of_mul_eq_one (4575 : ZMod 9151)
      decide
    · apply IsUnit.of_mul_eq_one (6492 : ZMod 9151)
      decide
    · apply IsUnit.of_mul_eq_one (8634 : ZMod 9151)
      decide
    · apply IsUnit.of_mul_eq_one (6104 : ZMod 9151)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_9157 : Nat.Prime 9157 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 9157 9156 1 6 [2, 2, 3, 7, 109]
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
    · apply IsUnit.of_mul_eq_one (4578 : ZMod 9157)
      decide
    · apply IsUnit.of_mul_eq_one (8725 : ZMod 9157)
      decide
    · apply IsUnit.of_mul_eq_one (6761 : ZMod 9157)
      decide
    · apply IsUnit.of_mul_eq_one (7139 : ZMod 9157)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_9161 : Nat.Prime 9161 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 9161 9160 1 3 [2, 2, 2, 5, 229]
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
    · apply IsUnit.of_mul_eq_one (4580 : ZMod 9161)
      decide
    · apply IsUnit.of_mul_eq_one (6445 : ZMod 9161)
      decide
    · apply IsUnit.of_mul_eq_one (6446 : ZMod 9161)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_9173 : Nat.Prime 9173 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 9173 9172 1 2 [2, 2, 2293]
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
    · apply IsUnit.of_mul_eq_one (4586 : ZMod 9173)
      decide
    · apply IsUnit.of_mul_eq_one (7950 : ZMod 9173)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_9181 : Nat.Prime 9181 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 9181 9180 1 2 [2, 2, 3, 3, 3, 5, 17]
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
    · apply IsUnit.of_mul_eq_one (4590 : ZMod 9181)
      decide
    · apply IsUnit.of_mul_eq_one (8844 : ZMod 9181)
      decide
    · apply IsUnit.of_mul_eq_one (2450 : ZMod 9181)
      decide
    · apply IsUnit.of_mul_eq_one (4952 : ZMod 9181)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_9187 : Nat.Prime 9187 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 9187 9186 1 3 [2, 3, 1531]
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
    · apply IsUnit.of_mul_eq_one (4593 : ZMod 9187)
      decide
    · apply IsUnit.of_mul_eq_one (1688 : ZMod 9187)
      decide
    · apply IsUnit.of_mul_eq_one (2587 : ZMod 9187)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_9199 : Nat.Prime 9199 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 9199 9198 1 3 [2, 3, 3, 7, 73]
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
    · apply IsUnit.of_mul_eq_one (4599 : ZMod 9199)
      decide
    · apply IsUnit.of_mul_eq_one (7388 : ZMod 9199)
      decide
    · apply IsUnit.of_mul_eq_one (6854 : ZMod 9199)
      decide
    · apply IsUnit.of_mul_eq_one (4952 : ZMod 9199)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_9203 : Nat.Prime 9203 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 9203 9202 1 2 [2, 43, 107]
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
    · apply IsUnit.of_mul_eq_one (4601 : ZMod 9203)
      decide
    · apply IsUnit.of_mul_eq_one (823 : ZMod 9203)
      decide
    · apply IsUnit.of_mul_eq_one (8760 : ZMod 9203)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_9209 : Nat.Prime 9209 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 9209 9208 1 3 [2, 2, 2, 1151]
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
    · apply IsUnit.of_mul_eq_one (4604 : ZMod 9209)
      decide
    · apply IsUnit.of_mul_eq_one (5378 : ZMod 9209)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_9221 : Nat.Prime 9221 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 9221 9220 1 2 [2, 2, 5, 461]
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
    · apply IsUnit.of_mul_eq_one (4610 : ZMod 9221)
      decide
    · apply IsUnit.of_mul_eq_one (3946 : ZMod 9221)
      decide
    · apply IsUnit.of_mul_eq_one (6091 : ZMod 9221)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_9227 : Nat.Prime 9227 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 9227 9226 1 2 [2, 7, 659]
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
    · apply IsUnit.of_mul_eq_one (4613 : ZMod 9227)
      decide
    · apply IsUnit.of_mul_eq_one (8015 : ZMod 9227)
      decide
    · apply IsUnit.of_mul_eq_one (3591 : ZMod 9227)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_9239 : Nat.Prime 9239 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 9239 9238 1 19 [2, 31, 149]
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
    · apply IsUnit.of_mul_eq_one (4619 : ZMod 9239)
      decide
    · apply IsUnit.of_mul_eq_one (8339 : ZMod 9239)
      decide
    · apply IsUnit.of_mul_eq_one (2649 : ZMod 9239)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_9241 : Nat.Prime 9241 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 9241 9240 1 13 [2, 2, 2, 3, 5, 7, 11]
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
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · apply IsUnit.of_mul_eq_one (4620 : ZMod 9241)
      decide
    · apply IsUnit.of_mul_eq_one (55 : ZMod 9241)
      decide
    · apply IsUnit.of_mul_eq_one (3810 : ZMod 9241)
      decide
    · apply IsUnit.of_mul_eq_one (7833 : ZMod 9241)
      decide
    · apply IsUnit.of_mul_eq_one (4937 : ZMod 9241)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_9257 : Nat.Prime 9257 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 9257 9256 1 3 [2, 2, 2, 13, 89]
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
    · apply IsUnit.of_mul_eq_one (4628 : ZMod 9257)
      decide
    · apply IsUnit.of_mul_eq_one (9089 : ZMod 9257)
      decide
    · apply IsUnit.of_mul_eq_one (2232 : ZMod 9257)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_9277 : Nat.Prime 9277 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 9277 9276 1 5 [2, 2, 3, 773]
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
    · apply IsUnit.of_mul_eq_one (4638 : ZMod 9277)
      decide
    · apply IsUnit.of_mul_eq_one (200 : ZMod 9277)
      decide
    · apply IsUnit.of_mul_eq_one (501 : ZMod 9277)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_9281 : Nat.Prime 9281 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 9281 9280 1 3 [2, 2, 2, 2, 2, 2, 5, 29]
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
    · apply IsUnit.of_mul_eq_one (4640 : ZMod 9281)
      decide
    · apply IsUnit.of_mul_eq_one (5274 : ZMod 9281)
      decide
    · apply IsUnit.of_mul_eq_one (2969 : ZMod 9281)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_9283 : Nat.Prime 9283 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 9283 9282 1 2 [2, 3, 7, 13, 17]
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
    · apply IsUnit.of_mul_eq_one (4641 : ZMod 9283)
      decide
    · apply IsUnit.of_mul_eq_one (7136 : ZMod 9283)
      decide
    · apply IsUnit.of_mul_eq_one (668 : ZMod 9283)
      decide
    · apply IsUnit.of_mul_eq_one (1880 : ZMod 9283)
      decide
    · apply IsUnit.of_mul_eq_one (5129 : ZMod 9283)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_9293 : Nat.Prime 9293 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 9293 9292 1 2 [2, 2, 23, 101]
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
    · apply IsUnit.of_mul_eq_one (4646 : ZMod 9293)
      decide
    · apply IsUnit.of_mul_eq_one (7818 : ZMod 9293)
      decide
    · apply IsUnit.of_mul_eq_one (9230 : ZMod 9293)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_9311 : Nat.Prime 9311 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 9311 9310 1 7 [2, 5, 7, 7, 19]
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
    · apply IsUnit.of_mul_eq_one (4655 : ZMod 9311)
      decide
    · apply IsUnit.of_mul_eq_one (2945 : ZMod 9311)
      decide
    · apply IsUnit.of_mul_eq_one (780 : ZMod 9311)
      decide
    · apply IsUnit.of_mul_eq_one (6720 : ZMod 9311)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_9319 : Nat.Prime 9319 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 9319 9318 1 3 [2, 3, 1553]
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
    · apply IsUnit.of_mul_eq_one (4659 : ZMod 9319)
      decide
    · apply IsUnit.of_mul_eq_one (5166 : ZMod 9319)
      decide
    · apply IsUnit.of_mul_eq_one (3085 : ZMod 9319)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_9323 : Nat.Prime 9323 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 9323 9322 1 2 [2, 59, 79]
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
    · apply IsUnit.of_mul_eq_one (4661 : ZMod 9323)
      decide
    · apply IsUnit.of_mul_eq_one (330 : ZMod 9323)
      decide
    · apply IsUnit.of_mul_eq_one (5173 : ZMod 9323)
      decide
  · norm_num

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

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_9403 : Nat.Prime 9403 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 9403 9402 1 3 [2, 3, 1567]
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
    · apply IsUnit.of_mul_eq_one (4701 : ZMod 9403)
      decide
    · apply IsUnit.of_mul_eq_one (1997 : ZMod 9403)
      decide
    · apply IsUnit.of_mul_eq_one (7091 : ZMod 9403)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_9413 : Nat.Prime 9413 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 9413 9412 1 3 [2, 2, 13, 181]
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
    · apply IsUnit.of_mul_eq_one (4706 : ZMod 9413)
      decide
    · apply IsUnit.of_mul_eq_one (6022 : ZMod 9413)
      decide
    · apply IsUnit.of_mul_eq_one (8893 : ZMod 9413)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_9419 : Nat.Prime 9419 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 9419 9418 1 2 [2, 17, 277]
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
    · apply IsUnit.of_mul_eq_one (4709 : ZMod 9419)
      decide
    · apply IsUnit.of_mul_eq_one (7868 : ZMod 9419)
      decide
    · apply IsUnit.of_mul_eq_one (2495 : ZMod 9419)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_9421 : Nat.Prime 9421 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 9421 9420 1 2 [2, 2, 3, 5, 157]
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
    · apply IsUnit.of_mul_eq_one (4710 : ZMod 9421)
      decide
    · apply IsUnit.of_mul_eq_one (5487 : ZMod 9421)
      decide
    · apply IsUnit.of_mul_eq_one (1422 : ZMod 9421)
      decide
    · apply IsUnit.of_mul_eq_one (5882 : ZMod 9421)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_9431 : Nat.Prime 9431 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 9431 9430 1 7 [2, 5, 23, 41]
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
    · apply IsUnit.of_mul_eq_one (4715 : ZMod 9431)
      decide
    · apply IsUnit.of_mul_eq_one (4550 : ZMod 9431)
      decide
    · apply IsUnit.of_mul_eq_one (7666 : ZMod 9431)
      decide
    · apply IsUnit.of_mul_eq_one (7711 : ZMod 9431)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_9433 : Nat.Prime 9433 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 9433 9432 1 5 [2, 2, 2, 3, 3, 131]
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
    · apply IsUnit.of_mul_eq_one (4716 : ZMod 9433)
      decide
    · apply IsUnit.of_mul_eq_one (2835 : ZMod 9433)
      decide
    · apply IsUnit.of_mul_eq_one (6104 : ZMod 9433)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_9437 : Nat.Prime 9437 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 9437 9436 1 2 [2, 2, 7, 337]
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
    · apply IsUnit.of_mul_eq_one (4718 : ZMod 9437)
      decide
    · apply IsUnit.of_mul_eq_one (5833 : ZMod 9437)
      decide
    · apply IsUnit.of_mul_eq_one (2831 : ZMod 9437)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_9439 : Nat.Prime 9439 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 9439 9438 1 22 [2, 3, 11, 11, 13]
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
    · apply IsUnit.of_mul_eq_one (4719 : ZMod 9439)
      decide
    · apply IsUnit.of_mul_eq_one (9194 : ZMod 9439)
      decide
    · apply IsUnit.of_mul_eq_one (4151 : ZMod 9439)
      decide
    · apply IsUnit.of_mul_eq_one (1818 : ZMod 9439)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_9461 : Nat.Prime 9461 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 9461 9460 1 3 [2, 2, 5, 11, 43]
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
    · apply IsUnit.of_mul_eq_one (4730 : ZMod 9461)
      decide
    · apply IsUnit.of_mul_eq_one (6536 : ZMod 9461)
      decide
    · apply IsUnit.of_mul_eq_one (9317 : ZMod 9461)
      decide
    · apply IsUnit.of_mul_eq_one (2783 : ZMod 9461)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_9463 : Nat.Prime 9463 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 9463 9462 1 3 [2, 3, 19, 83]
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
    · apply IsUnit.of_mul_eq_one (4731 : ZMod 9463)
      decide
    · apply IsUnit.of_mul_eq_one (9260 : ZMod 9463)
      decide
    · apply IsUnit.of_mul_eq_one (6531 : ZMod 9463)
      decide
    · apply IsUnit.of_mul_eq_one (6606 : ZMod 9463)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_9467 : Nat.Prime 9467 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 9467 9466 1 2 [2, 4733]
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
    · apply IsUnit.of_mul_eq_one (4733 : ZMod 9467)
      decide
    · apply IsUnit.of_mul_eq_one (3156 : ZMod 9467)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_9473 : Nat.Prime 9473 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 9473 9472 1 3 [2, 2, 2, 2, 2, 2, 2, 2, 37]
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
    · apply IsUnit.of_mul_eq_one (4736 : ZMod 9473)
      decide
    · apply IsUnit.of_mul_eq_one (5958 : ZMod 9473)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_9479 : Nat.Prime 9479 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 9479 9478 1 7 [2, 7, 677]
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
    · apply IsUnit.of_mul_eq_one (4739 : ZMod 9479)
      decide
    · apply IsUnit.of_mul_eq_one (1225 : ZMod 9479)
      decide
    · apply IsUnit.of_mul_eq_one (305 : ZMod 9479)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_9491 : Nat.Prime 9491 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 9491 9490 1 2 [2, 5, 13, 73]
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
    · apply IsUnit.of_mul_eq_one (4745 : ZMod 9491)
      decide
    · apply IsUnit.of_mul_eq_one (9089 : ZMod 9491)
      decide
    · apply IsUnit.of_mul_eq_one (1309 : ZMod 9491)
      decide
    · apply IsUnit.of_mul_eq_one (632 : ZMod 9491)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_9497 : Nat.Prime 9497 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 9497 9496 1 3 [2, 2, 2, 1187]
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
    · apply IsUnit.of_mul_eq_one (4748 : ZMod 9497)
      decide
    · apply IsUnit.of_mul_eq_one (4527 : ZMod 9497)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_9511 : Nat.Prime 9511 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 9511 9510 1 3 [2, 3, 5, 317]
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
    · apply IsUnit.of_mul_eq_one (4755 : ZMod 9511)
      decide
    · apply IsUnit.of_mul_eq_one (1163 : ZMod 9511)
      decide
    · apply IsUnit.of_mul_eq_one (786 : ZMod 9511)
      decide
    · apply IsUnit.of_mul_eq_one (6752 : ZMod 9511)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_9521 : Nat.Prime 9521 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 9521 9520 1 3 [2, 2, 2, 2, 5, 7, 17]
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
    · apply IsUnit.of_mul_eq_one (4760 : ZMod 9521)
      decide
    · apply IsUnit.of_mul_eq_one (9387 : ZMod 9521)
      decide
    · apply IsUnit.of_mul_eq_one (8547 : ZMod 9521)
      decide
    · apply IsUnit.of_mul_eq_one (8395 : ZMod 9521)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_9533 : Nat.Prime 9533 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 9533 9532 1 2 [2, 2, 2383]
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
    · apply IsUnit.of_mul_eq_one (4766 : ZMod 9533)
      decide
    · apply IsUnit.of_mul_eq_one (8262 : ZMod 9533)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_9539 : Nat.Prime 9539 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 9539 9538 1 2 [2, 19, 251]
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
    · apply IsUnit.of_mul_eq_one (4769 : ZMod 9539)
      decide
    · apply IsUnit.of_mul_eq_one (4413 : ZMod 9539)
      decide
    · apply IsUnit.of_mul_eq_one (4660 : ZMod 9539)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_9547 : Nat.Prime 9547 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 9547 9546 1 2 [2, 3, 37, 43]
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
    · apply IsUnit.of_mul_eq_one (4773 : ZMod 9547)
      decide
    · apply IsUnit.of_mul_eq_one (8457 : ZMod 9547)
      decide
    · apply IsUnit.of_mul_eq_one (1990 : ZMod 9547)
      decide
    · apply IsUnit.of_mul_eq_one (7471 : ZMod 9547)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_9551 : Nat.Prime 9551 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 9551 9550 1 11 [2, 5, 5, 191]
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
    · apply IsUnit.of_mul_eq_one (4775 : ZMod 9551)
      decide
    · apply IsUnit.of_mul_eq_one (1234 : ZMod 9551)
      decide
    · apply IsUnit.of_mul_eq_one (6753 : ZMod 9551)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_9587 : Nat.Prime 9587 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 9587 9586 1 2 [2, 4793]
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
    · apply IsUnit.of_mul_eq_one (4793 : ZMod 9587)
      decide
    · apply IsUnit.of_mul_eq_one (3196 : ZMod 9587)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_9601 : Nat.Prime 9601 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 9601 9600 1 13 [2, 2, 2, 2, 2, 2, 2, 3, 5, 5]
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
    · apply IsUnit.of_mul_eq_one (4800 : ZMod 9601)
      decide
    · apply IsUnit.of_mul_eq_one (4602 : ZMod 9601)
      decide
    · apply IsUnit.of_mul_eq_one (6151 : ZMod 9601)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_9613 : Nat.Prime 9613 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 9613 9612 1 2 [2, 2, 3, 3, 3, 89]
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
    · apply IsUnit.of_mul_eq_one (4806 : ZMod 9613)
      decide
    · apply IsUnit.of_mul_eq_one (2175 : ZMod 9613)
      decide
    · apply IsUnit.of_mul_eq_one (7292 : ZMod 9613)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_9619 : Nat.Prime 9619 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 9619 9618 1 2 [2, 3, 7, 229]
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
    · apply IsUnit.of_mul_eq_one (4809 : ZMod 9619)
      decide
    · apply IsUnit.of_mul_eq_one (1475 : ZMod 9619)
      decide
    · apply IsUnit.of_mul_eq_one (83 : ZMod 9619)
      decide
    · apply IsUnit.of_mul_eq_one (6054 : ZMod 9619)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_9623 : Nat.Prime 9623 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 9623 9622 1 5 [2, 17, 283]
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
    · apply IsUnit.of_mul_eq_one (4811 : ZMod 9623)
      decide
    · apply IsUnit.of_mul_eq_one (3337 : ZMod 9623)
      decide
    · apply IsUnit.of_mul_eq_one (1 : ZMod 9623)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_9629 : Nat.Prime 9629 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 9629 9628 1 2 [2, 2, 29, 83]
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
    · apply IsUnit.of_mul_eq_one (4814 : ZMod 9629)
      decide
    · apply IsUnit.of_mul_eq_one (3835 : ZMod 9629)
      decide
    · apply IsUnit.of_mul_eq_one (5865 : ZMod 9629)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_9631 : Nat.Prime 9631 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 9631 9630 1 3 [2, 3, 3, 5, 107]
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
    · apply IsUnit.of_mul_eq_one (4815 : ZMod 9631)
      decide
    · apply IsUnit.of_mul_eq_one (540 : ZMod 9631)
      decide
    · apply IsUnit.of_mul_eq_one (7676 : ZMod 9631)
      decide
    · apply IsUnit.of_mul_eq_one (4692 : ZMod 9631)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_9643 : Nat.Prime 9643 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 9643 9642 1 2 [2, 3, 1607]
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
    · apply IsUnit.of_mul_eq_one (4821 : ZMod 9643)
      decide
    · apply IsUnit.of_mul_eq_one (4896 : ZMod 9643)
      decide
    · apply IsUnit.of_mul_eq_one (7194 : ZMod 9643)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_9649 : Nat.Prime 9649 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 9649 9648 1 7 [2, 2, 2, 2, 3, 3, 67]
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
    · apply IsUnit.of_mul_eq_one (4824 : ZMod 9649)
      decide
    · apply IsUnit.of_mul_eq_one (1138 : ZMod 9649)
      decide
    · apply IsUnit.of_mul_eq_one (5118 : ZMod 9649)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_9661 : Nat.Prime 9661 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 9661 9660 1 2 [2, 2, 3, 5, 7, 23]
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
    · apply IsUnit.of_mul_eq_one (4830 : ZMod 9661)
      decide
    · apply IsUnit.of_mul_eq_one (5889 : ZMod 9661)
      decide
    · apply IsUnit.of_mul_eq_one (8128 : ZMod 9661)
      decide
    · apply IsUnit.of_mul_eq_one (2986 : ZMod 9661)
      decide
    · apply IsUnit.of_mul_eq_one (1303 : ZMod 9661)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_9677 : Nat.Prime 9677 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 9677 9676 1 2 [2, 2, 41, 59]
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
    · apply IsUnit.of_mul_eq_one (4838 : ZMod 9677)
      decide
    · apply IsUnit.of_mul_eq_one (1571 : ZMod 9677)
      decide
    · apply IsUnit.of_mul_eq_one (9626 : ZMod 9677)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_9679 : Nat.Prime 9679 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 9679 9678 1 3 [2, 3, 1613]
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
    · apply IsUnit.of_mul_eq_one (4839 : ZMod 9679)
      decide
    · apply IsUnit.of_mul_eq_one (5481 : ZMod 9679)
      decide
    · apply IsUnit.of_mul_eq_one (2566 : ZMod 9679)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_9689 : Nat.Prime 9689 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 9689 9688 1 3 [2, 2, 2, 7, 173]
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
    · apply IsUnit.of_mul_eq_one (4844 : ZMod 9689)
      decide
    · apply IsUnit.of_mul_eq_one (4638 : ZMod 9689)
      decide
    · apply IsUnit.of_mul_eq_one (5970 : ZMod 9689)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_9697 : Nat.Prime 9697 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 9697 9696 1 10 [2, 2, 2, 2, 2, 3, 101]
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
    · apply IsUnit.of_mul_eq_one (4848 : ZMod 9697)
      decide
    · apply IsUnit.of_mul_eq_one (7128 : ZMod 9697)
      decide
    · apply IsUnit.of_mul_eq_one (1400 : ZMod 9697)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_9719 : Nat.Prime 9719 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 9719 9718 1 17 [2, 43, 113]
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
    · apply IsUnit.of_mul_eq_one (4859 : ZMod 9719)
      decide
    · apply IsUnit.of_mul_eq_one (3035 : ZMod 9719)
      decide
    · apply IsUnit.of_mul_eq_one (4374 : ZMod 9719)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_9721 : Nat.Prime 9721 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 9721 9720 1 7 [2, 2, 2, 3, 3, 3, 3, 3, 5]
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
    · apply IsUnit.of_mul_eq_one (4860 : ZMod 9721)
      decide
    · apply IsUnit.of_mul_eq_one (641 : ZMod 9721)
      decide
    · apply IsUnit.of_mul_eq_one (4287 : ZMod 9721)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_9733 : Nat.Prime 9733 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 9733 9732 1 2 [2, 2, 3, 811]
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
    · apply IsUnit.of_mul_eq_one (4866 : ZMod 9733)
      decide
    · apply IsUnit.of_mul_eq_one (7005 : ZMod 9733)
      decide
    · apply IsUnit.of_mul_eq_one (3299 : ZMod 9733)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_9739 : Nat.Prime 9739 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 9739 9738 1 3 [2, 3, 3, 541]
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
    · apply IsUnit.of_mul_eq_one (4869 : ZMod 9739)
      decide
    · apply IsUnit.of_mul_eq_one (7415 : ZMod 9739)
      decide
    · apply IsUnit.of_mul_eq_one (2949 : ZMod 9739)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_9743 : Nat.Prime 9743 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 9743 9742 1 5 [2, 4871]
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
    · apply IsUnit.of_mul_eq_one (4871 : ZMod 9743)
      decide
    · apply IsUnit.of_mul_eq_one (406 : ZMod 9743)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_9749 : Nat.Prime 9749 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 9749 9748 1 2 [2, 2, 2437]
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
    · apply IsUnit.of_mul_eq_one (4874 : ZMod 9749)
      decide
    · apply IsUnit.of_mul_eq_one (650 : ZMod 9749)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_9767 : Nat.Prime 9767 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 9767 9766 1 5 [2, 19, 257]
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
    · apply IsUnit.of_mul_eq_one (4883 : ZMod 9767)
      decide
    · apply IsUnit.of_mul_eq_one (9426 : ZMod 9767)
      decide
    · apply IsUnit.of_mul_eq_one (7210 : ZMod 9767)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_9769 : Nat.Prime 9769 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 9769 9768 1 13 [2, 2, 2, 3, 11, 37]
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
    · apply IsUnit.of_mul_eq_one (4884 : ZMod 9769)
      decide
    · apply IsUnit.of_mul_eq_one (3343 : ZMod 9769)
      decide
    · apply IsUnit.of_mul_eq_one (740 : ZMod 9769)
      decide
    · apply IsUnit.of_mul_eq_one (7213 : ZMod 9769)
      decide
  · norm_num
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_8963_9418_part01 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_9414 (p := 8963) (q := 8969) (by exact lowPrime_8969) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9414 (p := 8969) (q := 8971) (by exact lowPrime_8971) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9414 (p := 8971) (q := 8999) (by exact lowPrime_8999) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9414 (p := 8999) (q := 9001) (by exact lowPrime_9001) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9414 (p := 9001) (q := 9007) (by exact lowPrime_9007) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9414 (p := 9007) (q := 9011) (by exact lowPrime_9011) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9414 (p := 9011) (q := 9013) (by exact lowPrime_9013) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9414 (p := 9013) (q := 9029) (by exact lowPrime_9029) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_8963_9418_part01_chain :
    DusartPrimeRowsChain 8963 9028 dusartPrimeRows_8963_9418_part01 := by
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

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_8963_9418_part02 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_9414 (p := 9029) (q := 9041) (by exact lowPrime_9041) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9414 (p := 9041) (q := 9043) (by exact lowPrime_9043) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9414 (p := 9043) (q := 9049) (by exact lowPrime_9049) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9414 (p := 9049) (q := 9059) (by exact lowPrime_9059) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9414 (p := 9059) (q := 9067) (by exact lowPrime_9067) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9414 (p := 9067) (q := 9091) (by exact lowPrime_9091) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9414 (p := 9091) (q := 9103) (by exact lowPrime_9103) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9414 (p := 9103) (q := 9109) (by exact lowPrime_9109) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_8963_9418_part02_chain :
    DusartPrimeRowsChain 9029 9108 dusartPrimeRows_8963_9418_part02 := by
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

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_8963_9418_part03 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_9414 (p := 9109) (q := 9127) (by exact lowPrime_9127) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9414 (p := 9127) (q := 9133) (by exact lowPrime_9133) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9414 (p := 9133) (q := 9137) (by exact lowPrime_9137) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9414 (p := 9137) (q := 9151) (by exact lowPrime_9151) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9414 (p := 9151) (q := 9157) (by exact lowPrime_9157) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9414 (p := 9157) (q := 9161) (by exact lowPrime_9161) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9414 (p := 9161) (q := 9173) (by exact lowPrime_9173) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9414 (p := 9173) (q := 9181) (by exact lowPrime_9181) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_8963_9418_part03_chain :
    DusartPrimeRowsChain 9109 9180 dusartPrimeRows_8963_9418_part03 := by
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

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_8963_9418_part04 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_9414 (p := 9181) (q := 9187) (by exact lowPrime_9187) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9414 (p := 9187) (q := 9199) (by exact lowPrime_9199) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9414 (p := 9199) (q := 9203) (by exact lowPrime_9203) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9414 (p := 9203) (q := 9209) (by exact lowPrime_9209) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9414 (p := 9209) (q := 9221) (by exact lowPrime_9221) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9414 (p := 9221) (q := 9227) (by exact lowPrime_9227) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9414 (p := 9227) (q := 9239) (by exact lowPrime_9239) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9414 (p := 9239) (q := 9241) (by exact lowPrime_9241) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_8963_9418_part04_chain :
    DusartPrimeRowsChain 9181 9240 dusartPrimeRows_8963_9418_part04 := by
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

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_8963_9418_part05 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_9414 (p := 9241) (q := 9257) (by exact lowPrime_9257) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9414 (p := 9257) (q := 9277) (by exact lowPrime_9277) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9414 (p := 9277) (q := 9281) (by exact lowPrime_9281) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9414 (p := 9281) (q := 9283) (by exact lowPrime_9283) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9414 (p := 9283) (q := 9293) (by exact lowPrime_9293) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9414 (p := 9293) (q := 9311) (by exact lowPrime_9311) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9414 (p := 9311) (q := 9319) (by exact lowPrime_9319) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9414 (p := 9319) (q := 9323) (by exact lowPrime_9323) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_8963_9418_part05_chain :
    DusartPrimeRowsChain 9241 9322 dusartPrimeRows_8963_9418_part05 := by
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

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_8963_9418_part07 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_9414 (p := 9397) (q := 9403) (by exact lowPrime_9403) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9414 (p := 9403) (q := 9413) (by exact lowPrime_9413) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9414 (p := 9413) (q := 9419) (by exact lowPrime_9419) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_8963_9418_part07_chain :
    DusartPrimeRowsChain 9397 9418 dusartPrimeRows_8963_9418_part07 := by
  apply DusartPrimeRowsChain.cons
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

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_9419_9900_part01 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_9897 (p := 9419) (q := 9421) (by exact lowPrime_9421) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9897 (p := 9421) (q := 9431) (by exact lowPrime_9431) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9897 (p := 9431) (q := 9433) (by exact lowPrime_9433) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9897 (p := 9433) (q := 9437) (by exact lowPrime_9437) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9897 (p := 9437) (q := 9439) (by exact lowPrime_9439) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9897 (p := 9439) (q := 9461) (by exact lowPrime_9461) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9897 (p := 9461) (q := 9463) (by exact lowPrime_9463) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9897 (p := 9463) (q := 9467) (by exact lowPrime_9467) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_9419_9900_part01_chain :
    DusartPrimeRowsChain 9419 9466 dusartPrimeRows_9419_9900_part01 := by
  apply DusartPrimeRowsChain.cons
  · norm_num [dusartPrimeRow_of_explicit_9897]
  · norm_num [dusartPrimeRow_of_explicit_9897]
  · apply DusartPrimeRowsChain.cons
    · norm_num [dusartPrimeRow_of_explicit_9897]
    · norm_num [dusartPrimeRow_of_explicit_9897]
    · apply DusartPrimeRowsChain.cons
      · norm_num [dusartPrimeRow_of_explicit_9897]
      · norm_num [dusartPrimeRow_of_explicit_9897]
      · apply DusartPrimeRowsChain.cons
        · norm_num [dusartPrimeRow_of_explicit_9897]
        · norm_num [dusartPrimeRow_of_explicit_9897]
        · apply DusartPrimeRowsChain.cons
          · norm_num [dusartPrimeRow_of_explicit_9897]
          · norm_num [dusartPrimeRow_of_explicit_9897]
          · apply DusartPrimeRowsChain.cons
            · norm_num [dusartPrimeRow_of_explicit_9897]
            · norm_num [dusartPrimeRow_of_explicit_9897]
            · apply DusartPrimeRowsChain.cons
              · norm_num [dusartPrimeRow_of_explicit_9897]
              · norm_num [dusartPrimeRow_of_explicit_9897]
              · apply DusartPrimeRowsChain.cons
                · norm_num [dusartPrimeRow_of_explicit_9897]
                · norm_num [dusartPrimeRow_of_explicit_9897]
                · apply DusartPrimeRowsChain.empty
                  norm_num [dusartPrimeRow_of_explicit_9897, dusartPrimeRow_of_explicit_right]

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_9419_9900_part02 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_9897 (p := 9467) (q := 9473) (by exact lowPrime_9473) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9897 (p := 9473) (q := 9479) (by exact lowPrime_9479) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9897 (p := 9479) (q := 9491) (by exact lowPrime_9491) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9897 (p := 9491) (q := 9497) (by exact lowPrime_9497) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9897 (p := 9497) (q := 9511) (by exact lowPrime_9511) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9897 (p := 9511) (q := 9521) (by exact lowPrime_9521) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9897 (p := 9521) (q := 9533) (by exact lowPrime_9533) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9897 (p := 9533) (q := 9539) (by exact lowPrime_9539) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_9419_9900_part02_chain :
    DusartPrimeRowsChain 9467 9538 dusartPrimeRows_9419_9900_part02 := by
  apply DusartPrimeRowsChain.cons
  · norm_num [dusartPrimeRow_of_explicit_9897]
  · norm_num [dusartPrimeRow_of_explicit_9897]
  · apply DusartPrimeRowsChain.cons
    · norm_num [dusartPrimeRow_of_explicit_9897]
    · norm_num [dusartPrimeRow_of_explicit_9897]
    · apply DusartPrimeRowsChain.cons
      · norm_num [dusartPrimeRow_of_explicit_9897]
      · norm_num [dusartPrimeRow_of_explicit_9897]
      · apply DusartPrimeRowsChain.cons
        · norm_num [dusartPrimeRow_of_explicit_9897]
        · norm_num [dusartPrimeRow_of_explicit_9897]
        · apply DusartPrimeRowsChain.cons
          · norm_num [dusartPrimeRow_of_explicit_9897]
          · norm_num [dusartPrimeRow_of_explicit_9897]
          · apply DusartPrimeRowsChain.cons
            · norm_num [dusartPrimeRow_of_explicit_9897]
            · norm_num [dusartPrimeRow_of_explicit_9897]
            · apply DusartPrimeRowsChain.cons
              · norm_num [dusartPrimeRow_of_explicit_9897]
              · norm_num [dusartPrimeRow_of_explicit_9897]
              · apply DusartPrimeRowsChain.cons
                · norm_num [dusartPrimeRow_of_explicit_9897]
                · norm_num [dusartPrimeRow_of_explicit_9897]
                · apply DusartPrimeRowsChain.empty
                  norm_num [dusartPrimeRow_of_explicit_9897, dusartPrimeRow_of_explicit_right]

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_9419_9900_part03 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_9897 (p := 9539) (q := 9547) (by exact lowPrime_9547) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9897 (p := 9547) (q := 9551) (by exact lowPrime_9551) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9897 (p := 9551) (q := 9587) (by exact lowPrime_9587) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9897 (p := 9587) (q := 9601) (by exact lowPrime_9601) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9897 (p := 9601) (q := 9613) (by exact lowPrime_9613) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9897 (p := 9613) (q := 9619) (by exact lowPrime_9619) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9897 (p := 9619) (q := 9623) (by exact lowPrime_9623) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9897 (p := 9623) (q := 9629) (by exact lowPrime_9629) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_9419_9900_part03_chain :
    DusartPrimeRowsChain 9539 9628 dusartPrimeRows_9419_9900_part03 := by
  apply DusartPrimeRowsChain.cons
  · norm_num [dusartPrimeRow_of_explicit_9897]
  · norm_num [dusartPrimeRow_of_explicit_9897]
  · apply DusartPrimeRowsChain.cons
    · norm_num [dusartPrimeRow_of_explicit_9897]
    · norm_num [dusartPrimeRow_of_explicit_9897]
    · apply DusartPrimeRowsChain.cons
      · norm_num [dusartPrimeRow_of_explicit_9897]
      · norm_num [dusartPrimeRow_of_explicit_9897]
      · apply DusartPrimeRowsChain.cons
        · norm_num [dusartPrimeRow_of_explicit_9897]
        · norm_num [dusartPrimeRow_of_explicit_9897]
        · apply DusartPrimeRowsChain.cons
          · norm_num [dusartPrimeRow_of_explicit_9897]
          · norm_num [dusartPrimeRow_of_explicit_9897]
          · apply DusartPrimeRowsChain.cons
            · norm_num [dusartPrimeRow_of_explicit_9897]
            · norm_num [dusartPrimeRow_of_explicit_9897]
            · apply DusartPrimeRowsChain.cons
              · norm_num [dusartPrimeRow_of_explicit_9897]
              · norm_num [dusartPrimeRow_of_explicit_9897]
              · apply DusartPrimeRowsChain.cons
                · norm_num [dusartPrimeRow_of_explicit_9897]
                · norm_num [dusartPrimeRow_of_explicit_9897]
                · apply DusartPrimeRowsChain.empty
                  norm_num [dusartPrimeRow_of_explicit_9897, dusartPrimeRow_of_explicit_right]

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_9419_9900_part04 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_9897 (p := 9629) (q := 9631) (by exact lowPrime_9631) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9897 (p := 9631) (q := 9643) (by exact lowPrime_9643) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9897 (p := 9643) (q := 9649) (by exact lowPrime_9649) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9897 (p := 9649) (q := 9661) (by exact lowPrime_9661) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9897 (p := 9661) (q := 9677) (by exact lowPrime_9677) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9897 (p := 9677) (q := 9679) (by exact lowPrime_9679) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9897 (p := 9679) (q := 9689) (by exact lowPrime_9689) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9897 (p := 9689) (q := 9697) (by exact lowPrime_9697) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_9419_9900_part04_chain :
    DusartPrimeRowsChain 9629 9696 dusartPrimeRows_9419_9900_part04 := by
  apply DusartPrimeRowsChain.cons
  · norm_num [dusartPrimeRow_of_explicit_9897]
  · norm_num [dusartPrimeRow_of_explicit_9897]
  · apply DusartPrimeRowsChain.cons
    · norm_num [dusartPrimeRow_of_explicit_9897]
    · norm_num [dusartPrimeRow_of_explicit_9897]
    · apply DusartPrimeRowsChain.cons
      · norm_num [dusartPrimeRow_of_explicit_9897]
      · norm_num [dusartPrimeRow_of_explicit_9897]
      · apply DusartPrimeRowsChain.cons
        · norm_num [dusartPrimeRow_of_explicit_9897]
        · norm_num [dusartPrimeRow_of_explicit_9897]
        · apply DusartPrimeRowsChain.cons
          · norm_num [dusartPrimeRow_of_explicit_9897]
          · norm_num [dusartPrimeRow_of_explicit_9897]
          · apply DusartPrimeRowsChain.cons
            · norm_num [dusartPrimeRow_of_explicit_9897]
            · norm_num [dusartPrimeRow_of_explicit_9897]
            · apply DusartPrimeRowsChain.cons
              · norm_num [dusartPrimeRow_of_explicit_9897]
              · norm_num [dusartPrimeRow_of_explicit_9897]
              · apply DusartPrimeRowsChain.cons
                · norm_num [dusartPrimeRow_of_explicit_9897]
                · norm_num [dusartPrimeRow_of_explicit_9897]
                · apply DusartPrimeRowsChain.empty
                  norm_num [dusartPrimeRow_of_explicit_9897, dusartPrimeRow_of_explicit_right]

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_9419_9900_part05 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_9897 (p := 9697) (q := 9719) (by exact lowPrime_9719) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9897 (p := 9719) (q := 9721) (by exact lowPrime_9721) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9897 (p := 9721) (q := 9733) (by exact lowPrime_9733) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9897 (p := 9733) (q := 9739) (by exact lowPrime_9739) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9897 (p := 9739) (q := 9743) (by exact lowPrime_9743) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9897 (p := 9743) (q := 9749) (by exact lowPrime_9749) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9897 (p := 9749) (q := 9767) (by exact lowPrime_9767) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9897 (p := 9767) (q := 9769) (by exact lowPrime_9769) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_9419_9900_part05_chain :
    DusartPrimeRowsChain 9697 9768 dusartPrimeRows_9419_9900_part05 := by
  apply DusartPrimeRowsChain.cons
  · norm_num [dusartPrimeRow_of_explicit_9897]
  · norm_num [dusartPrimeRow_of_explicit_9897]
  · apply DusartPrimeRowsChain.cons
    · norm_num [dusartPrimeRow_of_explicit_9897]
    · norm_num [dusartPrimeRow_of_explicit_9897]
    · apply DusartPrimeRowsChain.cons
      · norm_num [dusartPrimeRow_of_explicit_9897]
      · norm_num [dusartPrimeRow_of_explicit_9897]
      · apply DusartPrimeRowsChain.cons
        · norm_num [dusartPrimeRow_of_explicit_9897]
        · norm_num [dusartPrimeRow_of_explicit_9897]
        · apply DusartPrimeRowsChain.cons
          · norm_num [dusartPrimeRow_of_explicit_9897]
          · norm_num [dusartPrimeRow_of_explicit_9897]
          · apply DusartPrimeRowsChain.cons
            · norm_num [dusartPrimeRow_of_explicit_9897]
            · norm_num [dusartPrimeRow_of_explicit_9897]
            · apply DusartPrimeRowsChain.cons
              · norm_num [dusartPrimeRow_of_explicit_9897]
              · norm_num [dusartPrimeRow_of_explicit_9897]
              · apply DusartPrimeRowsChain.cons
                · norm_num [dusartPrimeRow_of_explicit_9897]
                · norm_num [dusartPrimeRow_of_explicit_9897]
                · apply DusartPrimeRowsChain.empty
                  norm_num [dusartPrimeRow_of_explicit_9897, dusartPrimeRow_of_explicit_right]
