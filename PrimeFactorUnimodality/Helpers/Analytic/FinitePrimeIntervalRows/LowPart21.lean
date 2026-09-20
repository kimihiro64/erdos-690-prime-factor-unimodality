import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowBase

set_option autoImplicit false
set_option maxRecDepth 1000000

/-! # Lower finite Dusart prefix chunk 21 -/

namespace PrimeFactorUnimodality

noncomputable section
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_18973 : Nat.Prime 18973 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 18973 18972 1 2 [2, 2, 3, 3, 17, 31]
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
    · apply IsUnit.of_mul_eq_one (9486 : ZMod 18973)
      decide
    · apply IsUnit.of_mul_eq_one (13563 : ZMod 18973)
      decide
    · apply IsUnit.of_mul_eq_one (4625 : ZMod 18973)
      decide
    · apply IsUnit.of_mul_eq_one (3084 : ZMod 18973)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_18979 : Nat.Prime 18979 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 18979 18978 1 2 [2, 3, 3163]
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
    · apply IsUnit.of_mul_eq_one (9489 : ZMod 18979)
      decide
    · apply IsUnit.of_mul_eq_one (12452 : ZMod 18979)
      decide
    · apply IsUnit.of_mul_eq_one (17774 : ZMod 18979)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_19001 : Nat.Prime 19001 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 19001 19000 1 3 [2, 2, 2, 5, 5, 5, 19]
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
    · apply IsUnit.of_mul_eq_one (9500 : ZMod 19001)
      decide
    · apply IsUnit.of_mul_eq_one (5749 : ZMod 19001)
      decide
    · apply IsUnit.of_mul_eq_one (16612 : ZMod 19001)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_19009 : Nat.Prime 19009 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 19009 19008 1 23 [2, 2, 2, 2, 2, 2, 3, 3, 3, 11]
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
    · apply IsUnit.of_mul_eq_one (9504 : ZMod 19009)
      decide
    · apply IsUnit.of_mul_eq_one (5794 : ZMod 19009)
      decide
    · apply IsUnit.of_mul_eq_one (17520 : ZMod 19009)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_19013 : Nat.Prime 19013 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 19013 19012 1 2 [2, 2, 7, 7, 97]
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
    · apply IsUnit.of_mul_eq_one (9506 : ZMod 19013)
      decide
    · apply IsUnit.of_mul_eq_one (1724 : ZMod 19013)
      decide
    · apply IsUnit.of_mul_eq_one (1428 : ZMod 19013)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_19031 : Nat.Prime 19031 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 19031 19030 1 11 [2, 5, 11, 173]
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
    · apply IsUnit.of_mul_eq_one (9515 : ZMod 19031)
      decide
    · apply IsUnit.of_mul_eq_one (9800 : ZMod 19031)
      decide
    · apply IsUnit.of_mul_eq_one (6465 : ZMod 19031)
      decide
    · apply IsUnit.of_mul_eq_one (14062 : ZMod 19031)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_19037 : Nat.Prime 19037 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 19037 19036 1 2 [2, 2, 4759]
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
    · apply IsUnit.of_mul_eq_one (9518 : ZMod 19037)
      decide
    · apply IsUnit.of_mul_eq_one (8884 : ZMod 19037)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_19051 : Nat.Prime 19051 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 19051 19050 1 2 [2, 3, 5, 5, 127]
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
    · apply IsUnit.of_mul_eq_one (9525 : ZMod 19051)
      decide
    · apply IsUnit.of_mul_eq_one (18052 : ZMod 19051)
      decide
    · apply IsUnit.of_mul_eq_one (7686 : ZMod 19051)
      decide
    · apply IsUnit.of_mul_eq_one (5299 : ZMod 19051)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_19069 : Nat.Prime 19069 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 19069 19068 1 2 [2, 2, 3, 7, 227]
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
    · apply IsUnit.of_mul_eq_one (9534 : ZMod 19069)
      decide
    · apply IsUnit.of_mul_eq_one (7307 : ZMod 19069)
      decide
    · apply IsUnit.of_mul_eq_one (16617 : ZMod 19069)
      decide
    · apply IsUnit.of_mul_eq_one (12176 : ZMod 19069)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_19073 : Nat.Prime 19073 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 19073 19072 1 3 [2, 2, 2, 2, 2, 2, 2, 149]
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
    · apply IsUnit.of_mul_eq_one (9536 : ZMod 19073)
      decide
    · apply IsUnit.of_mul_eq_one (1510 : ZMod 19073)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_19079 : Nat.Prime 19079 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 19079 19078 1 7 [2, 9539]
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
    · apply IsUnit.of_mul_eq_one (9539 : ZMod 19079)
      decide
    · apply IsUnit.of_mul_eq_one (9937 : ZMod 19079)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_19081 : Nat.Prime 19081 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 19081 19080 1 17 [2, 2, 2, 3, 3, 5, 53]
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
    · apply IsUnit.of_mul_eq_one (9540 : ZMod 19081)
      decide
    · apply IsUnit.of_mul_eq_one (4717 : ZMod 19081)
      decide
    · apply IsUnit.of_mul_eq_one (3487 : ZMod 19081)
      decide
    · apply IsUnit.of_mul_eq_one (1196 : ZMod 19081)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_19087 : Nat.Prime 19087 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 19087 19086 1 19 [2, 3, 3181]
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
    · apply IsUnit.of_mul_eq_one (9543 : ZMod 19087)
      decide
    · apply IsUnit.of_mul_eq_one (5065 : ZMod 19087)
      decide
    · apply IsUnit.of_mul_eq_one (7197 : ZMod 19087)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_19121 : Nat.Prime 19121 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 19121 19120 1 6 [2, 2, 2, 2, 5, 239]
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
    · apply IsUnit.of_mul_eq_one (9560 : ZMod 19121)
      decide
    · apply IsUnit.of_mul_eq_one (8245 : ZMod 19121)
      decide
    · apply IsUnit.of_mul_eq_one (133 : ZMod 19121)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_19139 : Nat.Prime 19139 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 19139 19138 1 2 [2, 7, 1367]
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
    · apply IsUnit.of_mul_eq_one (9569 : ZMod 19139)
      decide
    · apply IsUnit.of_mul_eq_one (9771 : ZMod 19139)
      decide
    · apply IsUnit.of_mul_eq_one (9632 : ZMod 19139)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_19141 : Nat.Prime 19141 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 19141 19140 1 2 [2, 2, 3, 5, 11, 29]
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
    · apply IsUnit.of_mul_eq_one (9570 : ZMod 19141)
      decide
    · apply IsUnit.of_mul_eq_one (9426 : ZMod 19141)
      decide
    · apply IsUnit.of_mul_eq_one (14590 : ZMod 19141)
      decide
    · apply IsUnit.of_mul_eq_one (5765 : ZMod 19141)
      decide
    · apply IsUnit.of_mul_eq_one (14172 : ZMod 19141)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_19157 : Nat.Prime 19157 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 19157 19156 1 2 [2, 2, 4789]
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
    · apply IsUnit.of_mul_eq_one (9578 : ZMod 19157)
      decide
    · apply IsUnit.of_mul_eq_one (8940 : ZMod 19157)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_19163 : Nat.Prime 19163 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 19163 19162 1 2 [2, 11, 13, 67]
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
    · apply IsUnit.of_mul_eq_one (9581 : ZMod 19163)
      decide
    · apply IsUnit.of_mul_eq_one (7900 : ZMod 19163)
      decide
    · apply IsUnit.of_mul_eq_one (18356 : ZMod 19163)
      decide
    · apply IsUnit.of_mul_eq_one (16250 : ZMod 19163)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_19181 : Nat.Prime 19181 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 19181 19180 1 2 [2, 2, 5, 7, 137]
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
    · apply IsUnit.of_mul_eq_one (9590 : ZMod 19181)
      decide
    · apply IsUnit.of_mul_eq_one (7499 : ZMod 19181)
      decide
    · apply IsUnit.of_mul_eq_one (5024 : ZMod 19181)
      decide
    · apply IsUnit.of_mul_eq_one (1837 : ZMod 19181)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_19183 : Nat.Prime 19183 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 19183 19182 1 3 [2, 3, 23, 139]
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
    · apply IsUnit.of_mul_eq_one (9591 : ZMod 19183)
      decide
    · apply IsUnit.of_mul_eq_one (12742 : ZMod 19183)
      decide
    · apply IsUnit.of_mul_eq_one (12216 : ZMod 19183)
      decide
    · apply IsUnit.of_mul_eq_one (7845 : ZMod 19183)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_19207 : Nat.Prime 19207 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 19207 19206 1 5 [2, 3, 3, 11, 97]
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
    · apply IsUnit.of_mul_eq_one (9603 : ZMod 19207)
      decide
    · apply IsUnit.of_mul_eq_one (15276 : ZMod 19207)
      decide
    · apply IsUnit.of_mul_eq_one (10698 : ZMod 19207)
      decide
    · apply IsUnit.of_mul_eq_one (13005 : ZMod 19207)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_19211 : Nat.Prime 19211 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 19211 19210 1 6 [2, 5, 17, 113]
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
    · apply IsUnit.of_mul_eq_one (9605 : ZMod 19211)
      decide
    · apply IsUnit.of_mul_eq_one (11344 : ZMod 19211)
      decide
    · apply IsUnit.of_mul_eq_one (7973 : ZMod 19211)
      decide
    · apply IsUnit.of_mul_eq_one (14290 : ZMod 19211)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_19213 : Nat.Prime 19213 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 19213 19212 1 5 [2, 2, 3, 1601]
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
    · apply IsUnit.of_mul_eq_one (9606 : ZMod 19213)
      decide
    · apply IsUnit.of_mul_eq_one (3407 : ZMod 19213)
      decide
    · apply IsUnit.of_mul_eq_one (14433 : ZMod 19213)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_19219 : Nat.Prime 19219 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 19219 19218 1 2 [2, 3, 3203]
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
    · apply IsUnit.of_mul_eq_one (9609 : ZMod 19219)
      decide
    · apply IsUnit.of_mul_eq_one (10060 : ZMod 19219)
      decide
    · apply IsUnit.of_mul_eq_one (14338 : ZMod 19219)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_19231 : Nat.Prime 19231 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 19231 19230 1 6 [2, 3, 5, 641]
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
    · apply IsUnit.of_mul_eq_one (9615 : ZMod 19231)
      decide
    · apply IsUnit.of_mul_eq_one (15942 : ZMod 19231)
      decide
    · apply IsUnit.of_mul_eq_one (12003 : ZMod 19231)
      decide
    · apply IsUnit.of_mul_eq_one (16463 : ZMod 19231)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_19237 : Nat.Prime 19237 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 19237 19236 1 2 [2, 2, 3, 7, 229]
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
    · apply IsUnit.of_mul_eq_one (9618 : ZMod 19237)
      decide
    · apply IsUnit.of_mul_eq_one (12521 : ZMod 19237)
      decide
    · apply IsUnit.of_mul_eq_one (12332 : ZMod 19237)
      decide
    · apply IsUnit.of_mul_eq_one (12275 : ZMod 19237)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_19249 : Nat.Prime 19249 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 19249 19248 1 7 [2, 2, 2, 2, 3, 401]
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
    · apply IsUnit.of_mul_eq_one (9624 : ZMod 19249)
      decide
    · apply IsUnit.of_mul_eq_one (4130 : ZMod 19249)
      decide
    · apply IsUnit.of_mul_eq_one (15997 : ZMod 19249)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_19259 : Nat.Prime 19259 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 19259 19258 1 2 [2, 9629]
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
    · apply IsUnit.of_mul_eq_one (9629 : ZMod 19259)
      decide
    · apply IsUnit.of_mul_eq_one (6420 : ZMod 19259)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_19267 : Nat.Prime 19267 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 19267 19266 1 3 [2, 3, 13, 13, 19]
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
    · apply IsUnit.of_mul_eq_one (9633 : ZMod 19267)
      decide
    · apply IsUnit.of_mul_eq_one (10461 : ZMod 19267)
      decide
    · apply IsUnit.of_mul_eq_one (17731 : ZMod 19267)
      decide
    · apply IsUnit.of_mul_eq_one (2619 : ZMod 19267)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_19273 : Nat.Prime 19273 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 19273 19272 1 5 [2, 2, 2, 3, 11, 73]
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
    · apply IsUnit.of_mul_eq_one (9636 : ZMod 19273)
      decide
    · apply IsUnit.of_mul_eq_one (13428 : ZMod 19273)
      decide
    · apply IsUnit.of_mul_eq_one (17576 : ZMod 19273)
      decide
    · apply IsUnit.of_mul_eq_one (4256 : ZMod 19273)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_19289 : Nat.Prime 19289 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 19289 19288 1 3 [2, 2, 2, 2411]
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
    · apply IsUnit.of_mul_eq_one (9644 : ZMod 19289)
      decide
    · apply IsUnit.of_mul_eq_one (444 : ZMod 19289)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_19301 : Nat.Prime 19301 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 19301 19300 1 2 [2, 2, 5, 5, 193]
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
    · apply IsUnit.of_mul_eq_one (9650 : ZMod 19301)
      decide
    · apply IsUnit.of_mul_eq_one (3175 : ZMod 19301)
      decide
    · apply IsUnit.of_mul_eq_one (17220 : ZMod 19301)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_19309 : Nat.Prime 19309 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 19309 19308 1 6 [2, 2, 3, 1609]
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
    · apply IsUnit.of_mul_eq_one (9654 : ZMod 19309)
      decide
    · apply IsUnit.of_mul_eq_one (9410 : ZMod 19309)
      decide
    · apply IsUnit.of_mul_eq_one (13020 : ZMod 19309)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_19319 : Nat.Prime 19319 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 19319 19318 1 11 [2, 13, 743]
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
    · apply IsUnit.of_mul_eq_one (9659 : ZMod 19319)
      decide
    · apply IsUnit.of_mul_eq_one (10676 : ZMod 19319)
      decide
    · apply IsUnit.of_mul_eq_one (13989 : ZMod 19319)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_19333 : Nat.Prime 19333 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 19333 19332 1 2 [2, 2, 3, 3, 3, 179]
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
    · apply IsUnit.of_mul_eq_one (9666 : ZMod 19333)
      decide
    · apply IsUnit.of_mul_eq_one (1599 : ZMod 19333)
      decide
    · apply IsUnit.of_mul_eq_one (2472 : ZMod 19333)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_19373 : Nat.Prime 19373 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 19373 19372 1 2 [2, 2, 29, 167]
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
    · apply IsUnit.of_mul_eq_one (9686 : ZMod 19373)
      decide
    · apply IsUnit.of_mul_eq_one (7830 : ZMod 19373)
      decide
    · apply IsUnit.of_mul_eq_one (6058 : ZMod 19373)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_19379 : Nat.Prime 19379 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 19379 19378 1 2 [2, 9689]
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
    · apply IsUnit.of_mul_eq_one (9689 : ZMod 19379)
      decide
    · apply IsUnit.of_mul_eq_one (6460 : ZMod 19379)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_19381 : Nat.Prime 19381 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 19381 19380 1 7 [2, 2, 3, 5, 17, 19]
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
    · apply IsUnit.of_mul_eq_one (9690 : ZMod 19381)
      decide
    · apply IsUnit.of_mul_eq_one (10401 : ZMod 19381)
      decide
    · apply IsUnit.of_mul_eq_one (4122 : ZMod 19381)
      decide
    · apply IsUnit.of_mul_eq_one (12635 : ZMod 19381)
      decide
    · apply IsUnit.of_mul_eq_one (241 : ZMod 19381)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_19387 : Nat.Prime 19387 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 19387 19386 1 2 [2, 3, 3, 3, 359]
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
    · apply IsUnit.of_mul_eq_one (9693 : ZMod 19387)
      decide
    · apply IsUnit.of_mul_eq_one (11875 : ZMod 19387)
      decide
    · apply IsUnit.of_mul_eq_one (16619 : ZMod 19387)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_19391 : Nat.Prime 19391 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 19391 19390 1 11 [2, 5, 7, 277]
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
    · apply IsUnit.of_mul_eq_one (9695 : ZMod 19391)
      decide
    · apply IsUnit.of_mul_eq_one (9063 : ZMod 19391)
      decide
    · apply IsUnit.of_mul_eq_one (7024 : ZMod 19391)
      decide
    · apply IsUnit.of_mul_eq_one (4910 : ZMod 19391)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_19403 : Nat.Prime 19403 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 19403 19402 1 2 [2, 89, 109]
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
    · apply IsUnit.of_mul_eq_one (9701 : ZMod 19403)
      decide
    · apply IsUnit.of_mul_eq_one (15694 : ZMod 19403)
      decide
    · apply IsUnit.of_mul_eq_one (17511 : ZMod 19403)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_19417 : Nat.Prime 19417 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 19417 19416 1 5 [2, 2, 2, 3, 809]
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
    · apply IsUnit.of_mul_eq_one (9708 : ZMod 19417)
      decide
    · apply IsUnit.of_mul_eq_one (7956 : ZMod 19417)
      decide
    · apply IsUnit.of_mul_eq_one (11767 : ZMod 19417)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_19421 : Nat.Prime 19421 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 19421 19420 1 3 [2, 2, 5, 971]
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
    · apply IsUnit.of_mul_eq_one (9710 : ZMod 19421)
      decide
    · apply IsUnit.of_mul_eq_one (1289 : ZMod 19421)
      decide
    · apply IsUnit.of_mul_eq_one (15803 : ZMod 19421)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_19423 : Nat.Prime 19423 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 19423 19422 1 3 [2, 3, 3, 13, 83]
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
    · apply IsUnit.of_mul_eq_one (9711 : ZMod 19423)
      decide
    · apply IsUnit.of_mul_eq_one (9935 : ZMod 19423)
      decide
    · apply IsUnit.of_mul_eq_one (14481 : ZMod 19423)
      decide
    · apply IsUnit.of_mul_eq_one (4825 : ZMod 19423)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_19427 : Nat.Prime 19427 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 19427 19426 1 2 [2, 11, 883]
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
    · apply IsUnit.of_mul_eq_one (9713 : ZMod 19427)
      decide
    · apply IsUnit.of_mul_eq_one (17632 : ZMod 19427)
      decide
    · apply IsUnit.of_mul_eq_one (15882 : ZMod 19427)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_19429 : Nat.Prime 19429 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 19429 19428 1 6 [2, 2, 3, 1619]
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
    · apply IsUnit.of_mul_eq_one (9714 : ZMod 19429)
      decide
    · apply IsUnit.of_mul_eq_one (5940 : ZMod 19429)
      decide
    · apply IsUnit.of_mul_eq_one (10863 : ZMod 19429)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_19433 : Nat.Prime 19433 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 19433 19432 1 3 [2, 2, 2, 7, 347]
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
    · apply IsUnit.of_mul_eq_one (9716 : ZMod 19433)
      decide
    · apply IsUnit.of_mul_eq_one (7278 : ZMod 19433)
      decide
    · apply IsUnit.of_mul_eq_one (14224 : ZMod 19433)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_19441 : Nat.Prime 19441 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 19441 19440 1 13 [2, 2, 2, 2, 3, 3, 3, 3, 3, 5]
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
    · apply IsUnit.of_mul_eq_one (9720 : ZMod 19441)
      decide
    · apply IsUnit.of_mul_eq_one (80 : ZMod 19441)
      decide
    · apply IsUnit.of_mul_eq_one (17601 : ZMod 19441)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_19447 : Nat.Prime 19447 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 19447 19446 1 3 [2, 3, 7, 463]
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
    · apply IsUnit.of_mul_eq_one (9723 : ZMod 19447)
      decide
    · apply IsUnit.of_mul_eq_one (15541 : ZMod 19447)
      decide
    · apply IsUnit.of_mul_eq_one (17278 : ZMod 19447)
      decide
    · apply IsUnit.of_mul_eq_one (8375 : ZMod 19447)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_19457 : Nat.Prime 19457 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 19457 19456 1 3 [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 19]
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
    · apply IsUnit.of_mul_eq_one (9728 : ZMod 19457)
      decide
    · apply IsUnit.of_mul_eq_one (13664 : ZMod 19457)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_19463 : Nat.Prime 19463 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 19463 19462 1 5 [2, 37, 263]
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
    · apply IsUnit.of_mul_eq_one (9731 : ZMod 19463)
      decide
    · apply IsUnit.of_mul_eq_one (4166 : ZMod 19463)
      decide
    · apply IsUnit.of_mul_eq_one (17962 : ZMod 19463)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_19469 : Nat.Prime 19469 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 19469 19468 1 2 [2, 2, 31, 157]
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
    · apply IsUnit.of_mul_eq_one (9734 : ZMod 19469)
      decide
    · apply IsUnit.of_mul_eq_one (2491 : ZMod 19469)
      decide
    · apply IsUnit.of_mul_eq_one (5531 : ZMod 19469)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_19471 : Nat.Prime 19471 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 19471 19470 1 11 [2, 3, 5, 11, 59]
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
    · apply IsUnit.of_mul_eq_one (9735 : ZMod 19471)
      decide
    · apply IsUnit.of_mul_eq_one (15923 : ZMod 19471)
      decide
    · apply IsUnit.of_mul_eq_one (7971 : ZMod 19471)
      decide
    · apply IsUnit.of_mul_eq_one (18792 : ZMod 19471)
      decide
    · apply IsUnit.of_mul_eq_one (6675 : ZMod 19471)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_19477 : Nat.Prime 19477 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 19477 19476 1 6 [2, 2, 3, 3, 541]
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
    · apply IsUnit.of_mul_eq_one (9738 : ZMod 19477)
      decide
    · apply IsUnit.of_mul_eq_one (14191 : ZMod 19477)
      decide
    · apply IsUnit.of_mul_eq_one (3042 : ZMod 19477)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_19483 : Nat.Prime 19483 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 19483 19482 1 2 [2, 3, 17, 191]
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
    · apply IsUnit.of_mul_eq_one (9741 : ZMod 19483)
      decide
    · apply IsUnit.of_mul_eq_one (1492 : ZMod 19483)
      decide
    · apply IsUnit.of_mul_eq_one (2681 : ZMod 19483)
      decide
    · apply IsUnit.of_mul_eq_one (2865 : ZMod 19483)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_19489 : Nat.Prime 19489 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 19489 19488 1 19 [2, 2, 2, 2, 2, 3, 7, 29]
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
    · apply IsUnit.of_mul_eq_one (9744 : ZMod 19489)
      decide
    · apply IsUnit.of_mul_eq_one (14332 : ZMod 19489)
      decide
    · apply IsUnit.of_mul_eq_one (4155 : ZMod 19489)
      decide
    · apply IsUnit.of_mul_eq_one (19205 : ZMod 19489)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_19501 : Nat.Prime 19501 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 19501 19500 1 2 [2, 2, 3, 5, 5, 5, 13]
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
    · apply IsUnit.of_mul_eq_one (9750 : ZMod 19501)
      decide
    · apply IsUnit.of_mul_eq_one (6332 : ZMod 19501)
      decide
    · apply IsUnit.of_mul_eq_one (9316 : ZMod 19501)
      decide
    · apply IsUnit.of_mul_eq_one (380 : ZMod 19501)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_19507 : Nat.Prime 19507 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 19507 19506 1 2 [2, 3, 3251]
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
    · apply IsUnit.of_mul_eq_one (9753 : ZMod 19507)
      decide
    · apply IsUnit.of_mul_eq_one (14280 : ZMod 19507)
      decide
    · apply IsUnit.of_mul_eq_one (3406 : ZMod 19507)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_19531 : Nat.Prime 19531 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 19531 19530 1 13 [2, 3, 3, 5, 7, 31]
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
    · apply IsUnit.of_mul_eq_one (9765 : ZMod 19531)
      decide
    · apply IsUnit.of_mul_eq_one (5135 : ZMod 19531)
      decide
    · apply IsUnit.of_mul_eq_one (6120 : ZMod 19531)
      decide
    · apply IsUnit.of_mul_eq_one (9922 : ZMod 19531)
      decide
    · apply IsUnit.of_mul_eq_one (95 : ZMod 19531)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_19541 : Nat.Prime 19541 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 19541 19540 1 2 [2, 2, 5, 977]
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
    · apply IsUnit.of_mul_eq_one (9770 : ZMod 19541)
      decide
    · apply IsUnit.of_mul_eq_one (4114 : ZMod 19541)
      decide
    · apply IsUnit.of_mul_eq_one (12421 : ZMod 19541)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_19543 : Nat.Prime 19543 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 19543 19542 1 3 [2, 3, 3257]
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
    · apply IsUnit.of_mul_eq_one (9771 : ZMod 19543)
      decide
    · apply IsUnit.of_mul_eq_one (2406 : ZMod 19543)
      decide
    · apply IsUnit.of_mul_eq_one (10550 : ZMod 19543)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_19553 : Nat.Prime 19553 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 19553 19552 1 3 [2, 2, 2, 2, 2, 13, 47]
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
    · apply IsUnit.of_mul_eq_one (9776 : ZMod 19553)
      decide
    · apply IsUnit.of_mul_eq_one (17889 : ZMod 19553)
      decide
    · apply IsUnit.of_mul_eq_one (15229 : ZMod 19553)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_19559 : Nat.Prime 19559 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 19559 19558 1 13 [2, 7, 11, 127]
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
    · apply IsUnit.of_mul_eq_one (9779 : ZMod 19559)
      decide
    · apply IsUnit.of_mul_eq_one (14646 : ZMod 19559)
      decide
    · apply IsUnit.of_mul_eq_one (3435 : ZMod 19559)
      decide
    · apply IsUnit.of_mul_eq_one (9643 : ZMod 19559)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_19571 : Nat.Prime 19571 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 19571 19570 1 2 [2, 5, 19, 103]
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
    · apply IsUnit.of_mul_eq_one (9785 : ZMod 19571)
      decide
    · apply IsUnit.of_mul_eq_one (15059 : ZMod 19571)
      decide
    · apply IsUnit.of_mul_eq_one (7401 : ZMod 19571)
      decide
    · apply IsUnit.of_mul_eq_one (359 : ZMod 19571)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_19577 : Nat.Prime 19577 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 19577 19576 1 3 [2, 2, 2, 2447]
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
    · apply IsUnit.of_mul_eq_one (9788 : ZMod 19577)
      decide
    · apply IsUnit.of_mul_eq_one (5512 : ZMod 19577)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_19583 : Nat.Prime 19583 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 19583 19582 1 5 [2, 9791]
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
    · apply IsUnit.of_mul_eq_one (9791 : ZMod 19583)
      decide
    · apply IsUnit.of_mul_eq_one (816 : ZMod 19583)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_19597 : Nat.Prime 19597 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 19597 19596 1 2 [2, 2, 3, 23, 71]
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
    · apply IsUnit.of_mul_eq_one (9798 : ZMod 19597)
      decide
    · apply IsUnit.of_mul_eq_one (14890 : ZMod 19597)
      decide
    · apply IsUnit.of_mul_eq_one (8114 : ZMod 19597)
      decide
    · apply IsUnit.of_mul_eq_one (16613 : ZMod 19597)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_19603 : Nat.Prime 19603 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 19603 19602 1 2 [2, 3, 3, 3, 3, 11, 11]
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
    · apply IsUnit.of_mul_eq_one (9801 : ZMod 19603)
      decide
    · apply IsUnit.of_mul_eq_one (16312 : ZMod 19603)
      decide
    · apply IsUnit.of_mul_eq_one (5002 : ZMod 19603)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_19609 : Nat.Prime 19609 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 19609 19608 1 13 [2, 2, 2, 3, 19, 43]
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
    · apply IsUnit.of_mul_eq_one (9804 : ZMod 19609)
      decide
    · apply IsUnit.of_mul_eq_one (291 : ZMod 19609)
      decide
    · apply IsUnit.of_mul_eq_one (3907 : ZMod 19609)
      decide
    · apply IsUnit.of_mul_eq_one (11242 : ZMod 19609)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_19661 : Nat.Prime 19661 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 19661 19660 1 2 [2, 2, 5, 983]
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
    · apply IsUnit.of_mul_eq_one (9830 : ZMod 19661)
      decide
    · apply IsUnit.of_mul_eq_one (7394 : ZMod 19661)
      decide
    · apply IsUnit.of_mul_eq_one (12920 : ZMod 19661)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_19681 : Nat.Prime 19681 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 19681 19680 1 11 [2, 2, 2, 2, 2, 3, 5, 41]
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
    · apply IsUnit.of_mul_eq_one (9840 : ZMod 19681)
      decide
    · apply IsUnit.of_mul_eq_one (15239 : ZMod 19681)
      decide
    · apply IsUnit.of_mul_eq_one (16439 : ZMod 19681)
      decide
    · apply IsUnit.of_mul_eq_one (10965 : ZMod 19681)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_19687 : Nat.Prime 19687 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 19687 19686 1 5 [2, 3, 17, 193]
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
    · apply IsUnit.of_mul_eq_one (9843 : ZMod 19687)
      decide
    · apply IsUnit.of_mul_eq_one (4901 : ZMod 19687)
      decide
    · apply IsUnit.of_mul_eq_one (6914 : ZMod 19687)
      decide
    · apply IsUnit.of_mul_eq_one (11946 : ZMod 19687)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_19697 : Nat.Prime 19697 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 19697 19696 1 3 [2, 2, 2, 2, 1231]
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
    · apply IsUnit.of_mul_eq_one (9848 : ZMod 19697)
      decide
    · apply IsUnit.of_mul_eq_one (2844 : ZMod 19697)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_19699 : Nat.Prime 19699 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 19699 19698 1 7 [2, 3, 7, 7, 67]
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
    · apply IsUnit.of_mul_eq_one (9849 : ZMod 19699)
      decide
    · apply IsUnit.of_mul_eq_one (2472 : ZMod 19699)
      decide
    · apply IsUnit.of_mul_eq_one (5376 : ZMod 19699)
      decide
    · apply IsUnit.of_mul_eq_one (15503 : ZMod 19699)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_19709 : Nat.Prime 19709 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 19709 19708 1 2 [2, 2, 13, 379]
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
    · apply IsUnit.of_mul_eq_one (9854 : ZMod 19709)
      decide
    · apply IsUnit.of_mul_eq_one (15451 : ZMod 19709)
      decide
    · apply IsUnit.of_mul_eq_one (11285 : ZMod 19709)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_19717 : Nat.Prime 19717 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 19717 19716 1 2 [2, 2, 3, 31, 53]
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
    · apply IsUnit.of_mul_eq_one (9858 : ZMod 19717)
      decide
    · apply IsUnit.of_mul_eq_one (17567 : ZMod 19717)
      decide
    · apply IsUnit.of_mul_eq_one (1846 : ZMod 19717)
      decide
    · apply IsUnit.of_mul_eq_one (4123 : ZMod 19717)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_19727 : Nat.Prime 19727 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 19727 19726 1 5 [2, 7, 1409]
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
    · apply IsUnit.of_mul_eq_one (9863 : ZMod 19727)
      decide
    · apply IsUnit.of_mul_eq_one (1401 : ZMod 19727)
      decide
    · apply IsUnit.of_mul_eq_one (2760 : ZMod 19727)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_19739 : Nat.Prime 19739 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 19739 19738 1 2 [2, 71, 139]
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
    · apply IsUnit.of_mul_eq_one (9869 : ZMod 19739)
      decide
    · apply IsUnit.of_mul_eq_one (12852 : ZMod 19739)
      decide
    · apply IsUnit.of_mul_eq_one (15472 : ZMod 19739)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_19751 : Nat.Prime 19751 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 19751 19750 1 7 [2, 5, 5, 5, 79]
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
    · apply IsUnit.of_mul_eq_one (9875 : ZMod 19751)
      decide
    · apply IsUnit.of_mul_eq_one (18719 : ZMod 19751)
      decide
    · apply IsUnit.of_mul_eq_one (14019 : ZMod 19751)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_19753 : Nat.Prime 19753 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 19753 19752 1 5 [2, 2, 2, 3, 823]
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
    · apply IsUnit.of_mul_eq_one (9876 : ZMod 19753)
      decide
    · apply IsUnit.of_mul_eq_one (17834 : ZMod 19753)
      decide
    · apply IsUnit.of_mul_eq_one (11041 : ZMod 19753)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_19759 : Nat.Prime 19759 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 19759 19758 1 3 [2, 3, 37, 89]
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
    · apply IsUnit.of_mul_eq_one (9879 : ZMod 19759)
      decide
    · apply IsUnit.of_mul_eq_one (10547 : ZMod 19759)
      decide
    · apply IsUnit.of_mul_eq_one (11806 : ZMod 19759)
      decide
    · apply IsUnit.of_mul_eq_one (14760 : ZMod 19759)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_19763 : Nat.Prime 19763 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 19763 19762 1 2 [2, 41, 241]
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
    · apply IsUnit.of_mul_eq_one (9881 : ZMod 19763)
      decide
    · apply IsUnit.of_mul_eq_one (19445 : ZMod 19763)
      decide
    · apply IsUnit.of_mul_eq_one (8419 : ZMod 19763)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_19777 : Nat.Prime 19777 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 19777 19776 1 11 [2, 2, 2, 2, 2, 2, 3, 103]
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
    · apply IsUnit.of_mul_eq_one (9888 : ZMod 19777)
      decide
    · apply IsUnit.of_mul_eq_one (4715 : ZMod 19777)
      decide
    · apply IsUnit.of_mul_eq_one (3596 : ZMod 19777)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_19793 : Nat.Prime 19793 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 19793 19792 1 3 [2, 2, 2, 2, 1237]
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
    · apply IsUnit.of_mul_eq_one (9896 : ZMod 19793)
      decide
    · apply IsUnit.of_mul_eq_one (6751 : ZMod 19793)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_19801 : Nat.Prime 19801 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 19801 19800 1 13 [2, 2, 2, 3, 3, 5, 5, 11]
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
    · apply IsUnit.of_mul_eq_one (9900 : ZMod 19801)
      decide
    · apply IsUnit.of_mul_eq_one (12472 : ZMod 19801)
      decide
    · apply IsUnit.of_mul_eq_one (7024 : ZMod 19801)
      decide
    · apply IsUnit.of_mul_eq_one (648 : ZMod 19801)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_19813 : Nat.Prime 19813 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 19813 19812 1 2 [2, 2, 3, 13, 127]
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
    · apply IsUnit.of_mul_eq_one (9906 : ZMod 19813)
      decide
    · apply IsUnit.of_mul_eq_one (17309 : ZMod 19813)
      decide
    · apply IsUnit.of_mul_eq_one (10292 : ZMod 19813)
      decide
    · apply IsUnit.of_mul_eq_one (6510 : ZMod 19813)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_19819 : Nat.Prime 19819 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 19819 19818 1 3 [2, 3, 3, 3, 367]
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
    · apply IsUnit.of_mul_eq_one (9909 : ZMod 19819)
      decide
    · apply IsUnit.of_mul_eq_one (2987 : ZMod 19819)
      decide
    · apply IsUnit.of_mul_eq_one (16472 : ZMod 19819)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_19841 : Nat.Prime 19841 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 19841 19840 1 3 [2, 2, 2, 2, 2, 2, 2, 5, 31]
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
    · apply IsUnit.of_mul_eq_one (9920 : ZMod 19841)
      decide
    · apply IsUnit.of_mul_eq_one (7627 : ZMod 19841)
      decide
    · apply IsUnit.of_mul_eq_one (4029 : ZMod 19841)
      decide
  · norm_num
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_18959_19936_part01 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_19930 (p := 18959) (q := 18973) (by exact lowPrime_18973) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_19930 (p := 18973) (q := 18979) (by exact lowPrime_18979) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_19930 (p := 18979) (q := 19001) (by exact lowPrime_19001) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_19930 (p := 19001) (q := 19009) (by exact lowPrime_19009) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_19930 (p := 19009) (q := 19013) (by exact lowPrime_19013) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_19930 (p := 19013) (q := 19031) (by exact lowPrime_19031) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_19930 (p := 19031) (q := 19037) (by exact lowPrime_19037) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_19930 (p := 19037) (q := 19051) (by exact lowPrime_19051) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_18959_19936_part01_chain :
    DusartPrimeRowsChain 18959 19050 dusartPrimeRows_18959_19936_part01 := by
  apply DusartPrimeRowsChain.cons
  · norm_num [dusartPrimeRow_of_explicit_19930]
  · norm_num [dusartPrimeRow_of_explicit_19930]
  · apply DusartPrimeRowsChain.cons
    · norm_num [dusartPrimeRow_of_explicit_19930]
    · norm_num [dusartPrimeRow_of_explicit_19930]
    · apply DusartPrimeRowsChain.cons
      · norm_num [dusartPrimeRow_of_explicit_19930]
      · norm_num [dusartPrimeRow_of_explicit_19930]
      · apply DusartPrimeRowsChain.cons
        · norm_num [dusartPrimeRow_of_explicit_19930]
        · norm_num [dusartPrimeRow_of_explicit_19930]
        · apply DusartPrimeRowsChain.cons
          · norm_num [dusartPrimeRow_of_explicit_19930]
          · norm_num [dusartPrimeRow_of_explicit_19930]
          · apply DusartPrimeRowsChain.cons
            · norm_num [dusartPrimeRow_of_explicit_19930]
            · norm_num [dusartPrimeRow_of_explicit_19930]
            · apply DusartPrimeRowsChain.cons
              · norm_num [dusartPrimeRow_of_explicit_19930]
              · norm_num [dusartPrimeRow_of_explicit_19930]
              · apply DusartPrimeRowsChain.cons
                · norm_num [dusartPrimeRow_of_explicit_19930]
                · norm_num [dusartPrimeRow_of_explicit_19930]
                · apply DusartPrimeRowsChain.empty
                  norm_num [dusartPrimeRow_of_explicit_19930, dusartPrimeRow_of_explicit_right]

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_18959_19936_part02 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_19930 (p := 19051) (q := 19069) (by exact lowPrime_19069) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_19930 (p := 19069) (q := 19073) (by exact lowPrime_19073) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_19930 (p := 19073) (q := 19079) (by exact lowPrime_19079) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_19930 (p := 19079) (q := 19081) (by exact lowPrime_19081) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_19930 (p := 19081) (q := 19087) (by exact lowPrime_19087) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_19930 (p := 19087) (q := 19121) (by exact lowPrime_19121) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_19930 (p := 19121) (q := 19139) (by exact lowPrime_19139) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_19930 (p := 19139) (q := 19141) (by exact lowPrime_19141) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_18959_19936_part02_chain :
    DusartPrimeRowsChain 19051 19140 dusartPrimeRows_18959_19936_part02 := by
  apply DusartPrimeRowsChain.cons
  · norm_num [dusartPrimeRow_of_explicit_19930]
  · norm_num [dusartPrimeRow_of_explicit_19930]
  · apply DusartPrimeRowsChain.cons
    · norm_num [dusartPrimeRow_of_explicit_19930]
    · norm_num [dusartPrimeRow_of_explicit_19930]
    · apply DusartPrimeRowsChain.cons
      · norm_num [dusartPrimeRow_of_explicit_19930]
      · norm_num [dusartPrimeRow_of_explicit_19930]
      · apply DusartPrimeRowsChain.cons
        · norm_num [dusartPrimeRow_of_explicit_19930]
        · norm_num [dusartPrimeRow_of_explicit_19930]
        · apply DusartPrimeRowsChain.cons
          · norm_num [dusartPrimeRow_of_explicit_19930]
          · norm_num [dusartPrimeRow_of_explicit_19930]
          · apply DusartPrimeRowsChain.cons
            · norm_num [dusartPrimeRow_of_explicit_19930]
            · norm_num [dusartPrimeRow_of_explicit_19930]
            · apply DusartPrimeRowsChain.cons
              · norm_num [dusartPrimeRow_of_explicit_19930]
              · norm_num [dusartPrimeRow_of_explicit_19930]
              · apply DusartPrimeRowsChain.cons
                · norm_num [dusartPrimeRow_of_explicit_19930]
                · norm_num [dusartPrimeRow_of_explicit_19930]
                · apply DusartPrimeRowsChain.empty
                  norm_num [dusartPrimeRow_of_explicit_19930, dusartPrimeRow_of_explicit_right]

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_18959_19936_part03 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_19930 (p := 19141) (q := 19157) (by exact lowPrime_19157) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_19930 (p := 19157) (q := 19163) (by exact lowPrime_19163) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_19930 (p := 19163) (q := 19181) (by exact lowPrime_19181) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_19930 (p := 19181) (q := 19183) (by exact lowPrime_19183) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_19930 (p := 19183) (q := 19207) (by exact lowPrime_19207) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_19930 (p := 19207) (q := 19211) (by exact lowPrime_19211) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_19930 (p := 19211) (q := 19213) (by exact lowPrime_19213) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_19930 (p := 19213) (q := 19219) (by exact lowPrime_19219) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_18959_19936_part03_chain :
    DusartPrimeRowsChain 19141 19218 dusartPrimeRows_18959_19936_part03 := by
  apply DusartPrimeRowsChain.cons
  · norm_num [dusartPrimeRow_of_explicit_19930]
  · norm_num [dusartPrimeRow_of_explicit_19930]
  · apply DusartPrimeRowsChain.cons
    · norm_num [dusartPrimeRow_of_explicit_19930]
    · norm_num [dusartPrimeRow_of_explicit_19930]
    · apply DusartPrimeRowsChain.cons
      · norm_num [dusartPrimeRow_of_explicit_19930]
      · norm_num [dusartPrimeRow_of_explicit_19930]
      · apply DusartPrimeRowsChain.cons
        · norm_num [dusartPrimeRow_of_explicit_19930]
        · norm_num [dusartPrimeRow_of_explicit_19930]
        · apply DusartPrimeRowsChain.cons
          · norm_num [dusartPrimeRow_of_explicit_19930]
          · norm_num [dusartPrimeRow_of_explicit_19930]
          · apply DusartPrimeRowsChain.cons
            · norm_num [dusartPrimeRow_of_explicit_19930]
            · norm_num [dusartPrimeRow_of_explicit_19930]
            · apply DusartPrimeRowsChain.cons
              · norm_num [dusartPrimeRow_of_explicit_19930]
              · norm_num [dusartPrimeRow_of_explicit_19930]
              · apply DusartPrimeRowsChain.cons
                · norm_num [dusartPrimeRow_of_explicit_19930]
                · norm_num [dusartPrimeRow_of_explicit_19930]
                · apply DusartPrimeRowsChain.empty
                  norm_num [dusartPrimeRow_of_explicit_19930, dusartPrimeRow_of_explicit_right]

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_18959_19936_part04 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_19930 (p := 19219) (q := 19231) (by exact lowPrime_19231) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_19930 (p := 19231) (q := 19237) (by exact lowPrime_19237) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_19930 (p := 19237) (q := 19249) (by exact lowPrime_19249) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_19930 (p := 19249) (q := 19259) (by exact lowPrime_19259) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_19930 (p := 19259) (q := 19267) (by exact lowPrime_19267) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_19930 (p := 19267) (q := 19273) (by exact lowPrime_19273) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_19930 (p := 19273) (q := 19289) (by exact lowPrime_19289) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_19930 (p := 19289) (q := 19301) (by exact lowPrime_19301) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_18959_19936_part04_chain :
    DusartPrimeRowsChain 19219 19300 dusartPrimeRows_18959_19936_part04 := by
  apply DusartPrimeRowsChain.cons
  · norm_num [dusartPrimeRow_of_explicit_19930]
  · norm_num [dusartPrimeRow_of_explicit_19930]
  · apply DusartPrimeRowsChain.cons
    · norm_num [dusartPrimeRow_of_explicit_19930]
    · norm_num [dusartPrimeRow_of_explicit_19930]
    · apply DusartPrimeRowsChain.cons
      · norm_num [dusartPrimeRow_of_explicit_19930]
      · norm_num [dusartPrimeRow_of_explicit_19930]
      · apply DusartPrimeRowsChain.cons
        · norm_num [dusartPrimeRow_of_explicit_19930]
        · norm_num [dusartPrimeRow_of_explicit_19930]
        · apply DusartPrimeRowsChain.cons
          · norm_num [dusartPrimeRow_of_explicit_19930]
          · norm_num [dusartPrimeRow_of_explicit_19930]
          · apply DusartPrimeRowsChain.cons
            · norm_num [dusartPrimeRow_of_explicit_19930]
            · norm_num [dusartPrimeRow_of_explicit_19930]
            · apply DusartPrimeRowsChain.cons
              · norm_num [dusartPrimeRow_of_explicit_19930]
              · norm_num [dusartPrimeRow_of_explicit_19930]
              · apply DusartPrimeRowsChain.cons
                · norm_num [dusartPrimeRow_of_explicit_19930]
                · norm_num [dusartPrimeRow_of_explicit_19930]
                · apply DusartPrimeRowsChain.empty
                  norm_num [dusartPrimeRow_of_explicit_19930, dusartPrimeRow_of_explicit_right]

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_18959_19936_part05 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_19930 (p := 19301) (q := 19309) (by exact lowPrime_19309) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_19930 (p := 19309) (q := 19319) (by exact lowPrime_19319) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_19930 (p := 19319) (q := 19333) (by exact lowPrime_19333) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_19930 (p := 19333) (q := 19373) (by exact lowPrime_19373) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_19930 (p := 19373) (q := 19379) (by exact lowPrime_19379) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_19930 (p := 19379) (q := 19381) (by exact lowPrime_19381) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_19930 (p := 19381) (q := 19387) (by exact lowPrime_19387) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_19930 (p := 19387) (q := 19391) (by exact lowPrime_19391) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_18959_19936_part05_chain :
    DusartPrimeRowsChain 19301 19390 dusartPrimeRows_18959_19936_part05 := by
  apply DusartPrimeRowsChain.cons
  · norm_num [dusartPrimeRow_of_explicit_19930]
  · norm_num [dusartPrimeRow_of_explicit_19930]
  · apply DusartPrimeRowsChain.cons
    · norm_num [dusartPrimeRow_of_explicit_19930]
    · norm_num [dusartPrimeRow_of_explicit_19930]
    · apply DusartPrimeRowsChain.cons
      · norm_num [dusartPrimeRow_of_explicit_19930]
      · norm_num [dusartPrimeRow_of_explicit_19930]
      · apply DusartPrimeRowsChain.cons
        · norm_num [dusartPrimeRow_of_explicit_19930]
        · norm_num [dusartPrimeRow_of_explicit_19930]
        · apply DusartPrimeRowsChain.cons
          · norm_num [dusartPrimeRow_of_explicit_19930]
          · norm_num [dusartPrimeRow_of_explicit_19930]
          · apply DusartPrimeRowsChain.cons
            · norm_num [dusartPrimeRow_of_explicit_19930]
            · norm_num [dusartPrimeRow_of_explicit_19930]
            · apply DusartPrimeRowsChain.cons
              · norm_num [dusartPrimeRow_of_explicit_19930]
              · norm_num [dusartPrimeRow_of_explicit_19930]
              · apply DusartPrimeRowsChain.cons
                · norm_num [dusartPrimeRow_of_explicit_19930]
                · norm_num [dusartPrimeRow_of_explicit_19930]
                · apply DusartPrimeRowsChain.empty
                  norm_num [dusartPrimeRow_of_explicit_19930, dusartPrimeRow_of_explicit_right]

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_18959_19936_part06 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_19930 (p := 19391) (q := 19403) (by exact lowPrime_19403) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_19930 (p := 19403) (q := 19417) (by exact lowPrime_19417) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_19930 (p := 19417) (q := 19421) (by exact lowPrime_19421) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_19930 (p := 19421) (q := 19423) (by exact lowPrime_19423) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_19930 (p := 19423) (q := 19427) (by exact lowPrime_19427) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_19930 (p := 19427) (q := 19429) (by exact lowPrime_19429) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_19930 (p := 19429) (q := 19433) (by exact lowPrime_19433) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_19930 (p := 19433) (q := 19441) (by exact lowPrime_19441) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_18959_19936_part06_chain :
    DusartPrimeRowsChain 19391 19440 dusartPrimeRows_18959_19936_part06 := by
  apply DusartPrimeRowsChain.cons
  · norm_num [dusartPrimeRow_of_explicit_19930]
  · norm_num [dusartPrimeRow_of_explicit_19930]
  · apply DusartPrimeRowsChain.cons
    · norm_num [dusartPrimeRow_of_explicit_19930]
    · norm_num [dusartPrimeRow_of_explicit_19930]
    · apply DusartPrimeRowsChain.cons
      · norm_num [dusartPrimeRow_of_explicit_19930]
      · norm_num [dusartPrimeRow_of_explicit_19930]
      · apply DusartPrimeRowsChain.cons
        · norm_num [dusartPrimeRow_of_explicit_19930]
        · norm_num [dusartPrimeRow_of_explicit_19930]
        · apply DusartPrimeRowsChain.cons
          · norm_num [dusartPrimeRow_of_explicit_19930]
          · norm_num [dusartPrimeRow_of_explicit_19930]
          · apply DusartPrimeRowsChain.cons
            · norm_num [dusartPrimeRow_of_explicit_19930]
            · norm_num [dusartPrimeRow_of_explicit_19930]
            · apply DusartPrimeRowsChain.cons
              · norm_num [dusartPrimeRow_of_explicit_19930]
              · norm_num [dusartPrimeRow_of_explicit_19930]
              · apply DusartPrimeRowsChain.cons
                · norm_num [dusartPrimeRow_of_explicit_19930]
                · norm_num [dusartPrimeRow_of_explicit_19930]
                · apply DusartPrimeRowsChain.empty
                  norm_num [dusartPrimeRow_of_explicit_19930, dusartPrimeRow_of_explicit_right]

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_18959_19936_part07 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_19930 (p := 19441) (q := 19447) (by exact lowPrime_19447) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_19930 (p := 19447) (q := 19457) (by exact lowPrime_19457) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_19930 (p := 19457) (q := 19463) (by exact lowPrime_19463) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_19930 (p := 19463) (q := 19469) (by exact lowPrime_19469) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_19930 (p := 19469) (q := 19471) (by exact lowPrime_19471) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_19930 (p := 19471) (q := 19477) (by exact lowPrime_19477) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_19930 (p := 19477) (q := 19483) (by exact lowPrime_19483) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_19930 (p := 19483) (q := 19489) (by exact lowPrime_19489) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_18959_19936_part07_chain :
    DusartPrimeRowsChain 19441 19488 dusartPrimeRows_18959_19936_part07 := by
  apply DusartPrimeRowsChain.cons
  · norm_num [dusartPrimeRow_of_explicit_19930]
  · norm_num [dusartPrimeRow_of_explicit_19930]
  · apply DusartPrimeRowsChain.cons
    · norm_num [dusartPrimeRow_of_explicit_19930]
    · norm_num [dusartPrimeRow_of_explicit_19930]
    · apply DusartPrimeRowsChain.cons
      · norm_num [dusartPrimeRow_of_explicit_19930]
      · norm_num [dusartPrimeRow_of_explicit_19930]
      · apply DusartPrimeRowsChain.cons
        · norm_num [dusartPrimeRow_of_explicit_19930]
        · norm_num [dusartPrimeRow_of_explicit_19930]
        · apply DusartPrimeRowsChain.cons
          · norm_num [dusartPrimeRow_of_explicit_19930]
          · norm_num [dusartPrimeRow_of_explicit_19930]
          · apply DusartPrimeRowsChain.cons
            · norm_num [dusartPrimeRow_of_explicit_19930]
            · norm_num [dusartPrimeRow_of_explicit_19930]
            · apply DusartPrimeRowsChain.cons
              · norm_num [dusartPrimeRow_of_explicit_19930]
              · norm_num [dusartPrimeRow_of_explicit_19930]
              · apply DusartPrimeRowsChain.cons
                · norm_num [dusartPrimeRow_of_explicit_19930]
                · norm_num [dusartPrimeRow_of_explicit_19930]
                · apply DusartPrimeRowsChain.empty
                  norm_num [dusartPrimeRow_of_explicit_19930, dusartPrimeRow_of_explicit_right]

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_18959_19936_part08 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_19930 (p := 19489) (q := 19501) (by exact lowPrime_19501) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_19930 (p := 19501) (q := 19507) (by exact lowPrime_19507) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_19930 (p := 19507) (q := 19531) (by exact lowPrime_19531) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_19930 (p := 19531) (q := 19541) (by exact lowPrime_19541) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_19930 (p := 19541) (q := 19543) (by exact lowPrime_19543) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_19930 (p := 19543) (q := 19553) (by exact lowPrime_19553) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_19930 (p := 19553) (q := 19559) (by exact lowPrime_19559) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_19930 (p := 19559) (q := 19571) (by exact lowPrime_19571) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_18959_19936_part08_chain :
    DusartPrimeRowsChain 19489 19570 dusartPrimeRows_18959_19936_part08 := by
  apply DusartPrimeRowsChain.cons
  · norm_num [dusartPrimeRow_of_explicit_19930]
  · norm_num [dusartPrimeRow_of_explicit_19930]
  · apply DusartPrimeRowsChain.cons
    · norm_num [dusartPrimeRow_of_explicit_19930]
    · norm_num [dusartPrimeRow_of_explicit_19930]
    · apply DusartPrimeRowsChain.cons
      · norm_num [dusartPrimeRow_of_explicit_19930]
      · norm_num [dusartPrimeRow_of_explicit_19930]
      · apply DusartPrimeRowsChain.cons
        · norm_num [dusartPrimeRow_of_explicit_19930]
        · norm_num [dusartPrimeRow_of_explicit_19930]
        · apply DusartPrimeRowsChain.cons
          · norm_num [dusartPrimeRow_of_explicit_19930]
          · norm_num [dusartPrimeRow_of_explicit_19930]
          · apply DusartPrimeRowsChain.cons
            · norm_num [dusartPrimeRow_of_explicit_19930]
            · norm_num [dusartPrimeRow_of_explicit_19930]
            · apply DusartPrimeRowsChain.cons
              · norm_num [dusartPrimeRow_of_explicit_19930]
              · norm_num [dusartPrimeRow_of_explicit_19930]
              · apply DusartPrimeRowsChain.cons
                · norm_num [dusartPrimeRow_of_explicit_19930]
                · norm_num [dusartPrimeRow_of_explicit_19930]
                · apply DusartPrimeRowsChain.empty
                  norm_num [dusartPrimeRow_of_explicit_19930, dusartPrimeRow_of_explicit_right]

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_18959_19936_part09 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_19930 (p := 19571) (q := 19577) (by exact lowPrime_19577) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_19930 (p := 19577) (q := 19583) (by exact lowPrime_19583) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_19930 (p := 19583) (q := 19597) (by exact lowPrime_19597) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_19930 (p := 19597) (q := 19603) (by exact lowPrime_19603) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_19930 (p := 19603) (q := 19609) (by exact lowPrime_19609) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_19930 (p := 19609) (q := 19661) (by exact lowPrime_19661) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_19930 (p := 19661) (q := 19681) (by exact lowPrime_19681) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_19930 (p := 19681) (q := 19687) (by exact lowPrime_19687) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_18959_19936_part09_chain :
    DusartPrimeRowsChain 19571 19686 dusartPrimeRows_18959_19936_part09 := by
  apply DusartPrimeRowsChain.cons
  · norm_num [dusartPrimeRow_of_explicit_19930]
  · norm_num [dusartPrimeRow_of_explicit_19930]
  · apply DusartPrimeRowsChain.cons
    · norm_num [dusartPrimeRow_of_explicit_19930]
    · norm_num [dusartPrimeRow_of_explicit_19930]
    · apply DusartPrimeRowsChain.cons
      · norm_num [dusartPrimeRow_of_explicit_19930]
      · norm_num [dusartPrimeRow_of_explicit_19930]
      · apply DusartPrimeRowsChain.cons
        · norm_num [dusartPrimeRow_of_explicit_19930]
        · norm_num [dusartPrimeRow_of_explicit_19930]
        · apply DusartPrimeRowsChain.cons
          · norm_num [dusartPrimeRow_of_explicit_19930]
          · norm_num [dusartPrimeRow_of_explicit_19930]
          · apply DusartPrimeRowsChain.cons
            · norm_num [dusartPrimeRow_of_explicit_19930]
            · norm_num [dusartPrimeRow_of_explicit_19930]
            · apply DusartPrimeRowsChain.cons
              · norm_num [dusartPrimeRow_of_explicit_19930]
              · norm_num [dusartPrimeRow_of_explicit_19930]
              · apply DusartPrimeRowsChain.cons
                · norm_num [dusartPrimeRow_of_explicit_19930]
                · norm_num [dusartPrimeRow_of_explicit_19930]
                · apply DusartPrimeRowsChain.empty
                  norm_num [dusartPrimeRow_of_explicit_19930, dusartPrimeRow_of_explicit_right]

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_18959_19936_part10 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_19930 (p := 19687) (q := 19697) (by exact lowPrime_19697) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_19930 (p := 19697) (q := 19699) (by exact lowPrime_19699) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_19930 (p := 19699) (q := 19709) (by exact lowPrime_19709) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_19930 (p := 19709) (q := 19717) (by exact lowPrime_19717) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_19930 (p := 19717) (q := 19727) (by exact lowPrime_19727) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_19930 (p := 19727) (q := 19739) (by exact lowPrime_19739) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_19930 (p := 19739) (q := 19751) (by exact lowPrime_19751) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_19930 (p := 19751) (q := 19753) (by exact lowPrime_19753) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_18959_19936_part10_chain :
    DusartPrimeRowsChain 19687 19752 dusartPrimeRows_18959_19936_part10 := by
  apply DusartPrimeRowsChain.cons
  · norm_num [dusartPrimeRow_of_explicit_19930]
  · norm_num [dusartPrimeRow_of_explicit_19930]
  · apply DusartPrimeRowsChain.cons
    · norm_num [dusartPrimeRow_of_explicit_19930]
    · norm_num [dusartPrimeRow_of_explicit_19930]
    · apply DusartPrimeRowsChain.cons
      · norm_num [dusartPrimeRow_of_explicit_19930]
      · norm_num [dusartPrimeRow_of_explicit_19930]
      · apply DusartPrimeRowsChain.cons
        · norm_num [dusartPrimeRow_of_explicit_19930]
        · norm_num [dusartPrimeRow_of_explicit_19930]
        · apply DusartPrimeRowsChain.cons
          · norm_num [dusartPrimeRow_of_explicit_19930]
          · norm_num [dusartPrimeRow_of_explicit_19930]
          · apply DusartPrimeRowsChain.cons
            · norm_num [dusartPrimeRow_of_explicit_19930]
            · norm_num [dusartPrimeRow_of_explicit_19930]
            · apply DusartPrimeRowsChain.cons
              · norm_num [dusartPrimeRow_of_explicit_19930]
              · norm_num [dusartPrimeRow_of_explicit_19930]
              · apply DusartPrimeRowsChain.cons
                · norm_num [dusartPrimeRow_of_explicit_19930]
                · norm_num [dusartPrimeRow_of_explicit_19930]
                · apply DusartPrimeRowsChain.empty
                  norm_num [dusartPrimeRow_of_explicit_19930, dusartPrimeRow_of_explicit_right]

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_18959_19936_part11 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_19930 (p := 19753) (q := 19759) (by exact lowPrime_19759) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_19930 (p := 19759) (q := 19763) (by exact lowPrime_19763) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_19930 (p := 19763) (q := 19777) (by exact lowPrime_19777) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_19930 (p := 19777) (q := 19793) (by exact lowPrime_19793) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_19930 (p := 19793) (q := 19801) (by exact lowPrime_19801) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_19930 (p := 19801) (q := 19813) (by exact lowPrime_19813) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_19930 (p := 19813) (q := 19819) (by exact lowPrime_19819) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_19930 (p := 19819) (q := 19841) (by exact lowPrime_19841) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_18959_19936_part11_chain :
    DusartPrimeRowsChain 19753 19840 dusartPrimeRows_18959_19936_part11 := by
  apply DusartPrimeRowsChain.cons
  · norm_num [dusartPrimeRow_of_explicit_19930]
  · norm_num [dusartPrimeRow_of_explicit_19930]
  · apply DusartPrimeRowsChain.cons
    · norm_num [dusartPrimeRow_of_explicit_19930]
    · norm_num [dusartPrimeRow_of_explicit_19930]
    · apply DusartPrimeRowsChain.cons
      · norm_num [dusartPrimeRow_of_explicit_19930]
      · norm_num [dusartPrimeRow_of_explicit_19930]
      · apply DusartPrimeRowsChain.cons
        · norm_num [dusartPrimeRow_of_explicit_19930]
        · norm_num [dusartPrimeRow_of_explicit_19930]
        · apply DusartPrimeRowsChain.cons
          · norm_num [dusartPrimeRow_of_explicit_19930]
          · norm_num [dusartPrimeRow_of_explicit_19930]
          · apply DusartPrimeRowsChain.cons
            · norm_num [dusartPrimeRow_of_explicit_19930]
            · norm_num [dusartPrimeRow_of_explicit_19930]
            · apply DusartPrimeRowsChain.cons
              · norm_num [dusartPrimeRow_of_explicit_19930]
              · norm_num [dusartPrimeRow_of_explicit_19930]
              · apply DusartPrimeRowsChain.cons
                · norm_num [dusartPrimeRow_of_explicit_19930]
                · norm_num [dusartPrimeRow_of_explicit_19930]
                · apply DusartPrimeRowsChain.empty
                  norm_num [dusartPrimeRow_of_explicit_19930, dusartPrimeRow_of_explicit_right]
