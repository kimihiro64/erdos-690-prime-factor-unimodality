import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowBase

set_option autoImplicit false
set_option maxRecDepth 1000000

/-! # Lower finite Dusart prefix chunk 22 -/

namespace PrimeFactorUnimodality

noncomputable section
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_18043 : Nat.Prime 18043 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 18043 18042 1 2 [2, 3, 31, 97]
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
    · apply IsUnit.of_mul_eq_one (9021 : ZMod 18043)
      decide
    · apply IsUnit.of_mul_eq_one (14098 : ZMod 18043)
      decide
    · apply IsUnit.of_mul_eq_one (8385 : ZMod 18043)
      decide
    · apply IsUnit.of_mul_eq_one (860 : ZMod 18043)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_18047 : Nat.Prime 18047 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 18047 18046 1 5 [2, 7, 1289]
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
    · apply IsUnit.of_mul_eq_one (9023 : ZMod 18047)
      decide
    · apply IsUnit.of_mul_eq_one (17111 : ZMod 18047)
      decide
    · apply IsUnit.of_mul_eq_one (572 : ZMod 18047)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_18049 : Nat.Prime 18049 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 18049 18048 1 13 [2, 2, 2, 2, 2, 2, 2, 3, 47]
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
    · apply IsUnit.of_mul_eq_one (9024 : ZMod 18049)
      decide
    · apply IsUnit.of_mul_eq_one (13119 : ZMod 18049)
      decide
    · apply IsUnit.of_mul_eq_one (3873 : ZMod 18049)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_18059 : Nat.Prime 18059 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 18059 18058 1 2 [2, 9029]
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
    · apply IsUnit.of_mul_eq_one (9029 : ZMod 18059)
      decide
    · apply IsUnit.of_mul_eq_one (6020 : ZMod 18059)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_18061 : Nat.Prime 18061 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 18061 18060 1 6 [2, 2, 3, 5, 7, 43]
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
    · apply IsUnit.of_mul_eq_one (9030 : ZMod 18061)
      decide
    · apply IsUnit.of_mul_eq_one (11108 : ZMod 18061)
      decide
    · apply IsUnit.of_mul_eq_one (939 : ZMod 18061)
      decide
    · apply IsUnit.of_mul_eq_one (14576 : ZMod 18061)
      decide
    · apply IsUnit.of_mul_eq_one (17703 : ZMod 18061)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_18077 : Nat.Prime 18077 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 18077 18076 1 2 [2, 2, 4519]
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
    · apply IsUnit.of_mul_eq_one (9038 : ZMod 18077)
      decide
    · apply IsUnit.of_mul_eq_one (8436 : ZMod 18077)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_18089 : Nat.Prime 18089 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 18089 18088 1 3 [2, 2, 2, 7, 17, 19]
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
    · apply IsUnit.of_mul_eq_one (9044 : ZMod 18089)
      decide
    · apply IsUnit.of_mul_eq_one (1018 : ZMod 18089)
      decide
    · apply IsUnit.of_mul_eq_one (9477 : ZMod 18089)
      decide
    · apply IsUnit.of_mul_eq_one (7795 : ZMod 18089)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_18097 : Nat.Prime 18097 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 18097 18096 1 5 [2, 2, 2, 2, 3, 13, 29]
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
    · apply IsUnit.of_mul_eq_one (9048 : ZMod 18097)
      decide
    · apply IsUnit.of_mul_eq_one (14060 : ZMod 18097)
      decide
    · apply IsUnit.of_mul_eq_one (16363 : ZMod 18097)
      decide
    · apply IsUnit.of_mul_eq_one (10916 : ZMod 18097)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_18119 : Nat.Prime 18119 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 18119 18118 1 17 [2, 9059]
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
    · apply IsUnit.of_mul_eq_one (9059 : ZMod 18119)
      decide
    · apply IsUnit.of_mul_eq_one (16672 : ZMod 18119)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_18121 : Nat.Prime 18121 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 18121 18120 1 23 [2, 2, 2, 3, 5, 151]
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
    · apply IsUnit.of_mul_eq_one (9060 : ZMod 18121)
      decide
    · apply IsUnit.of_mul_eq_one (12330 : ZMod 18121)
      decide
    · apply IsUnit.of_mul_eq_one (15075 : ZMod 18121)
      decide
    · apply IsUnit.of_mul_eq_one (11791 : ZMod 18121)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_18127 : Nat.Prime 18127 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 18127 18126 1 3 [2, 3, 3, 19, 53]
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
    · apply IsUnit.of_mul_eq_one (9063 : ZMod 18127)
      decide
    · apply IsUnit.of_mul_eq_one (8625 : ZMod 18127)
      decide
    · apply IsUnit.of_mul_eq_one (9151 : ZMod 18127)
      decide
    · apply IsUnit.of_mul_eq_one (7244 : ZMod 18127)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_18131 : Nat.Prime 18131 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 18131 18130 1 7 [2, 5, 7, 7, 37]
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
    · apply IsUnit.of_mul_eq_one (9065 : ZMod 18131)
      decide
    · apply IsUnit.of_mul_eq_one (4996 : ZMod 18131)
      decide
    · apply IsUnit.of_mul_eq_one (10679 : ZMod 18131)
      decide
    · apply IsUnit.of_mul_eq_one (11177 : ZMod 18131)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_18133 : Nat.Prime 18133 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 18133 18132 1 5 [2, 2, 3, 1511]
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
    · apply IsUnit.of_mul_eq_one (9066 : ZMod 18133)
      decide
    · apply IsUnit.of_mul_eq_one (1176 : ZMod 18133)
      decide
    · apply IsUnit.of_mul_eq_one (2614 : ZMod 18133)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_18143 : Nat.Prime 18143 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 18143 18142 1 5 [2, 47, 193]
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
    · apply IsUnit.of_mul_eq_one (9071 : ZMod 18143)
      decide
    · apply IsUnit.of_mul_eq_one (5780 : ZMod 18143)
      decide
    · apply IsUnit.of_mul_eq_one (1879 : ZMod 18143)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_18149 : Nat.Prime 18149 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 18149 18148 1 2 [2, 2, 13, 349]
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
    · apply IsUnit.of_mul_eq_one (9074 : ZMod 18149)
      decide
    · apply IsUnit.of_mul_eq_one (13400 : ZMod 18149)
      decide
    · apply IsUnit.of_mul_eq_one (4583 : ZMod 18149)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_18169 : Nat.Prime 18169 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 18169 18168 1 11 [2, 2, 2, 3, 757]
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
    · apply IsUnit.of_mul_eq_one (9084 : ZMod 18169)
      decide
    · apply IsUnit.of_mul_eq_one (2191 : ZMod 18169)
      decide
    · apply IsUnit.of_mul_eq_one (3494 : ZMod 18169)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_18181 : Nat.Prime 18181 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 18181 18180 1 2 [2, 2, 3, 3, 5, 101]
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
    · apply IsUnit.of_mul_eq_one (9090 : ZMod 18181)
      decide
    · apply IsUnit.of_mul_eq_one (3852 : ZMod 18181)
      decide
    · apply IsUnit.of_mul_eq_one (1019 : ZMod 18181)
      decide
    · apply IsUnit.of_mul_eq_one (13973 : ZMod 18181)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_18191 : Nat.Prime 18191 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 18191 18190 1 29 [2, 5, 17, 107]
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
    · apply IsUnit.of_mul_eq_one (9095 : ZMod 18191)
      decide
    · apply IsUnit.of_mul_eq_one (166 : ZMod 18191)
      decide
    · apply IsUnit.of_mul_eq_one (960 : ZMod 18191)
      decide
    · apply IsUnit.of_mul_eq_one (4925 : ZMod 18191)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_18199 : Nat.Prime 18199 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 18199 18198 1 11 [2, 3, 3, 3, 337]
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
    · apply IsUnit.of_mul_eq_one (9099 : ZMod 18199)
      decide
    · apply IsUnit.of_mul_eq_one (339 : ZMod 18199)
      decide
    · apply IsUnit.of_mul_eq_one (7826 : ZMod 18199)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_18211 : Nat.Prime 18211 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 18211 18210 1 7 [2, 3, 5, 607]
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
    · apply IsUnit.of_mul_eq_one (9105 : ZMod 18211)
      decide
    · apply IsUnit.of_mul_eq_one (17518 : ZMod 18211)
      decide
    · apply IsUnit.of_mul_eq_one (7603 : ZMod 18211)
      decide
    · apply IsUnit.of_mul_eq_one (3102 : ZMod 18211)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_18217 : Nat.Prime 18217 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 18217 18216 1 7 [2, 2, 2, 3, 3, 11, 23]
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
    · apply IsUnit.of_mul_eq_one (9108 : ZMod 18217)
      decide
    · apply IsUnit.of_mul_eq_one (9345 : ZMod 18217)
      decide
    · apply IsUnit.of_mul_eq_one (9454 : ZMod 18217)
      decide
    · apply IsUnit.of_mul_eq_one (8815 : ZMod 18217)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_18223 : Nat.Prime 18223 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 18223 18222 1 3 [2, 3, 3037]
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
    · apply IsUnit.of_mul_eq_one (9111 : ZMod 18223)
      decide
    · apply IsUnit.of_mul_eq_one (11424 : ZMod 18223)
      decide
    · apply IsUnit.of_mul_eq_one (15845 : ZMod 18223)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_18229 : Nat.Prime 18229 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 18229 18228 1 2 [2, 2, 3, 7, 7, 31]
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
    · apply IsUnit.of_mul_eq_one (9114 : ZMod 18229)
      decide
    · apply IsUnit.of_mul_eq_one (16974 : ZMod 18229)
      decide
    · apply IsUnit.of_mul_eq_one (17385 : ZMod 18229)
      decide
    · apply IsUnit.of_mul_eq_one (3809 : ZMod 18229)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_18233 : Nat.Prime 18233 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 18233 18232 1 3 [2, 2, 2, 43, 53]
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
    · apply IsUnit.of_mul_eq_one (9116 : ZMod 18233)
      decide
    · apply IsUnit.of_mul_eq_one (13150 : ZMod 18233)
      decide
    · apply IsUnit.of_mul_eq_one (438 : ZMod 18233)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_18251 : Nat.Prime 18251 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 18251 18250 1 2 [2, 5, 5, 5, 73]
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
    · apply IsUnit.of_mul_eq_one (9125 : ZMod 18251)
      decide
    · apply IsUnit.of_mul_eq_one (4597 : ZMod 18251)
      decide
    · apply IsUnit.of_mul_eq_one (2194 : ZMod 18251)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_18253 : Nat.Prime 18253 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 18253 18252 1 5 [2, 2, 3, 3, 3, 13, 13]
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
    · apply IsUnit.of_mul_eq_one (9126 : ZMod 18253)
      decide
    · apply IsUnit.of_mul_eq_one (9087 : ZMod 18253)
      decide
    · apply IsUnit.of_mul_eq_one (2928 : ZMod 18253)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_18257 : Nat.Prime 18257 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 18257 18256 1 5 [2, 2, 2, 2, 7, 163]
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
    · apply IsUnit.of_mul_eq_one (9128 : ZMod 18257)
      decide
    · apply IsUnit.of_mul_eq_one (4491 : ZMod 18257)
      decide
    · apply IsUnit.of_mul_eq_one (4217 : ZMod 18257)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_18269 : Nat.Prime 18269 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 18269 18268 1 2 [2, 2, 4567]
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
    · apply IsUnit.of_mul_eq_one (9134 : ZMod 18269)
      decide
    · apply IsUnit.of_mul_eq_one (1218 : ZMod 18269)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_18287 : Nat.Prime 18287 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 18287 18286 1 5 [2, 41, 223]
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
    · apply IsUnit.of_mul_eq_one (9143 : ZMod 18287)
      decide
    · apply IsUnit.of_mul_eq_one (10760 : ZMod 18287)
      decide
    · apply IsUnit.of_mul_eq_one (5113 : ZMod 18287)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_18289 : Nat.Prime 18289 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 18289 18288 1 13 [2, 2, 2, 2, 3, 3, 127]
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
    · apply IsUnit.of_mul_eq_one (9144 : ZMod 18289)
      decide
    · apply IsUnit.of_mul_eq_one (13275 : ZMod 18289)
      decide
    · apply IsUnit.of_mul_eq_one (8872 : ZMod 18289)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_18301 : Nat.Prime 18301 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 18301 18300 1 6 [2, 2, 3, 5, 5, 61]
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
    · apply IsUnit.of_mul_eq_one (9150 : ZMod 18301)
      decide
    · apply IsUnit.of_mul_eq_one (6530 : ZMod 18301)
      decide
    · apply IsUnit.of_mul_eq_one (11614 : ZMod 18301)
      decide
    · apply IsUnit.of_mul_eq_one (4247 : ZMod 18301)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_18307 : Nat.Prime 18307 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 18307 18306 1 11 [2, 3, 3, 3, 3, 113]
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
    · apply IsUnit.of_mul_eq_one (9153 : ZMod 18307)
      decide
    · apply IsUnit.of_mul_eq_one (7894 : ZMod 18307)
      decide
    · apply IsUnit.of_mul_eq_one (8525 : ZMod 18307)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_18311 : Nat.Prime 18311 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 18311 18310 1 13 [2, 5, 1831]
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
    · apply IsUnit.of_mul_eq_one (9155 : ZMod 18311)
      decide
    · apply IsUnit.of_mul_eq_one (2654 : ZMod 18311)
      decide
    · apply IsUnit.of_mul_eq_one (3709 : ZMod 18311)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_18313 : Nat.Prime 18313 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 18313 18312 1 10 [2, 2, 2, 3, 7, 109]
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
    · apply IsUnit.of_mul_eq_one (9156 : ZMod 18313)
      decide
    · apply IsUnit.of_mul_eq_one (997 : ZMod 18313)
      decide
    · apply IsUnit.of_mul_eq_one (9675 : ZMod 18313)
      decide
    · apply IsUnit.of_mul_eq_one (2521 : ZMod 18313)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_18329 : Nat.Prime 18329 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 18329 18328 1 3 [2, 2, 2, 29, 79]
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
    · apply IsUnit.of_mul_eq_one (9164 : ZMod 18329)
      decide
    · apply IsUnit.of_mul_eq_one (11378 : ZMod 18329)
      decide
    · apply IsUnit.of_mul_eq_one (9344 : ZMod 18329)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_18341 : Nat.Prime 18341 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 18341 18340 1 3 [2, 2, 5, 7, 131]
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
    · apply IsUnit.of_mul_eq_one (9170 : ZMod 18341)
      decide
    · apply IsUnit.of_mul_eq_one (10579 : ZMod 18341)
      decide
    · apply IsUnit.of_mul_eq_one (12998 : ZMod 18341)
      decide
    · apply IsUnit.of_mul_eq_one (4363 : ZMod 18341)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_18353 : Nat.Prime 18353 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 18353 18352 1 3 [2, 2, 2, 2, 31, 37]
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
    · apply IsUnit.of_mul_eq_one (9176 : ZMod 18353)
      decide
    · apply IsUnit.of_mul_eq_one (8481 : ZMod 18353)
      decide
    · apply IsUnit.of_mul_eq_one (5670 : ZMod 18353)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_18367 : Nat.Prime 18367 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 18367 18366 1 3 [2, 3, 3061]
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
    · apply IsUnit.of_mul_eq_one (9183 : ZMod 18367)
      decide
    · apply IsUnit.of_mul_eq_one (4066 : ZMod 18367)
      decide
    · apply IsUnit.of_mul_eq_one (11328 : ZMod 18367)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_18371 : Nat.Prime 18371 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 18371 18370 1 11 [2, 5, 11, 167]
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
    · apply IsUnit.of_mul_eq_one (9185 : ZMod 18371)
      decide
    · apply IsUnit.of_mul_eq_one (8990 : ZMod 18371)
      decide
    · apply IsUnit.of_mul_eq_one (17496 : ZMod 18371)
      decide
    · apply IsUnit.of_mul_eq_one (11524 : ZMod 18371)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_18379 : Nat.Prime 18379 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 18379 18378 1 3 [2, 3, 3, 1021]
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
    · apply IsUnit.of_mul_eq_one (9189 : ZMod 18379)
      decide
    · apply IsUnit.of_mul_eq_one (15937 : ZMod 18379)
      decide
    · apply IsUnit.of_mul_eq_one (3136 : ZMod 18379)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_18397 : Nat.Prime 18397 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 18397 18396 1 6 [2, 2, 3, 3, 7, 73]
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
    · apply IsUnit.of_mul_eq_one (9198 : ZMod 18397)
      decide
    · apply IsUnit.of_mul_eq_one (882 : ZMod 18397)
      decide
    · apply IsUnit.of_mul_eq_one (2579 : ZMod 18397)
      decide
    · apply IsUnit.of_mul_eq_one (125 : ZMod 18397)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_18401 : Nat.Prime 18401 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 18401 18400 1 3 [2, 2, 2, 2, 2, 5, 5, 23]
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
    · apply IsUnit.of_mul_eq_one (9200 : ZMod 18401)
      decide
    · apply IsUnit.of_mul_eq_one (818 : ZMod 18401)
      decide
    · apply IsUnit.of_mul_eq_one (6221 : ZMod 18401)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_18413 : Nat.Prime 18413 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 18413 18412 1 2 [2, 2, 4603]
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
    · apply IsUnit.of_mul_eq_one (9206 : ZMod 18413)
      decide
    · apply IsUnit.of_mul_eq_one (15958 : ZMod 18413)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_18427 : Nat.Prime 18427 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 18427 18426 1 2 [2, 3, 37, 83]
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
    · apply IsUnit.of_mul_eq_one (9213 : ZMod 18427)
      decide
    · apply IsUnit.of_mul_eq_one (5620 : ZMod 18427)
      decide
    · apply IsUnit.of_mul_eq_one (17644 : ZMod 18427)
      decide
    · apply IsUnit.of_mul_eq_one (6299 : ZMod 18427)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_18433 : Nat.Prime 18433 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 18433 18432 1 5 [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 3, 3]
  · norm_num
  · norm_num
  · norm_num
  · intro p hp
    simp at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals decide
  · norm_num
  · norm_num
  · decide
  · intro q hq
    simp at hq
    rcases hq with rfl | rfl
    · apply IsUnit.of_mul_eq_one (9216 : ZMod 18433)
      decide
    · apply IsUnit.of_mul_eq_one (1261 : ZMod 18433)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_18439 : Nat.Prime 18439 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 18439 18438 1 3 [2, 3, 7, 439]
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
    · apply IsUnit.of_mul_eq_one (9219 : ZMod 18439)
      decide
    · apply IsUnit.of_mul_eq_one (15742 : ZMod 18439)
      decide
    · apply IsUnit.of_mul_eq_one (10852 : ZMod 18439)
      decide
    · apply IsUnit.of_mul_eq_one (11356 : ZMod 18439)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_18443 : Nat.Prime 18443 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 18443 18442 1 2 [2, 9221]
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
    · apply IsUnit.of_mul_eq_one (9221 : ZMod 18443)
      decide
    · apply IsUnit.of_mul_eq_one (6148 : ZMod 18443)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_18451 : Nat.Prime 18451 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 18451 18450 1 3 [2, 3, 3, 5, 5, 41]
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
    · apply IsUnit.of_mul_eq_one (9225 : ZMod 18451)
      decide
    · apply IsUnit.of_mul_eq_one (2791 : ZMod 18451)
      decide
    · apply IsUnit.of_mul_eq_one (1554 : ZMod 18451)
      decide
    · apply IsUnit.of_mul_eq_one (10309 : ZMod 18451)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_18457 : Nat.Prime 18457 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 18457 18456 1 5 [2, 2, 2, 3, 769]
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
    · apply IsUnit.of_mul_eq_one (9228 : ZMod 18457)
      decide
    · apply IsUnit.of_mul_eq_one (6730 : ZMod 18457)
      decide
    · apply IsUnit.of_mul_eq_one (3407 : ZMod 18457)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_18461 : Nat.Prime 18461 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 18461 18460 1 2 [2, 2, 5, 13, 71]
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
    · apply IsUnit.of_mul_eq_one (9230 : ZMod 18461)
      decide
    · apply IsUnit.of_mul_eq_one (9097 : ZMod 18461)
      decide
    · apply IsUnit.of_mul_eq_one (14440 : ZMod 18461)
      decide
    · apply IsUnit.of_mul_eq_one (3619 : ZMod 18461)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_18481 : Nat.Prime 18481 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 18481 18480 1 13 [2, 2, 2, 2, 3, 5, 7, 11]
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
    · apply IsUnit.of_mul_eq_one (9240 : ZMod 18481)
      decide
    · apply IsUnit.of_mul_eq_one (13751 : ZMod 18481)
      decide
    · apply IsUnit.of_mul_eq_one (3806 : ZMod 18481)
      decide
    · apply IsUnit.of_mul_eq_one (160 : ZMod 18481)
      decide
    · apply IsUnit.of_mul_eq_one (12344 : ZMod 18481)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_18493 : Nat.Prime 18493 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 18493 18492 1 2 [2, 2, 3, 23, 67]
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
    · apply IsUnit.of_mul_eq_one (9246 : ZMod 18493)
      decide
    · apply IsUnit.of_mul_eq_one (7381 : ZMod 18493)
      decide
    · apply IsUnit.of_mul_eq_one (3325 : ZMod 18493)
      decide
    · apply IsUnit.of_mul_eq_one (164 : ZMod 18493)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_18503 : Nat.Prime 18503 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 18503 18502 1 5 [2, 11, 29, 29]
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
    · apply IsUnit.of_mul_eq_one (9251 : ZMod 18503)
      decide
    · apply IsUnit.of_mul_eq_one (8656 : ZMod 18503)
      decide
    · apply IsUnit.of_mul_eq_one (18083 : ZMod 18503)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_18517 : Nat.Prime 18517 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 18517 18516 1 6 [2, 2, 3, 1543]
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
    · apply IsUnit.of_mul_eq_one (9258 : ZMod 18517)
      decide
    · apply IsUnit.of_mul_eq_one (1690 : ZMod 18517)
      decide
    · apply IsUnit.of_mul_eq_one (13715 : ZMod 18517)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_18521 : Nat.Prime 18521 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 18521 18520 1 3 [2, 2, 2, 5, 463]
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
    · apply IsUnit.of_mul_eq_one (9260 : ZMod 18521)
      decide
    · apply IsUnit.of_mul_eq_one (4206 : ZMod 18521)
      decide
    · apply IsUnit.of_mul_eq_one (315 : ZMod 18521)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_18523 : Nat.Prime 18523 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 18523 18522 1 3 [2, 3, 3, 3, 7, 7, 7]
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
    · apply IsUnit.of_mul_eq_one (9261 : ZMod 18523)
      decide
    · apply IsUnit.of_mul_eq_one (1021 : ZMod 18523)
      decide
    · apply IsUnit.of_mul_eq_one (17556 : ZMod 18523)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_18539 : Nat.Prime 18539 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 18539 18538 1 6 [2, 13, 23, 31]
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
    · apply IsUnit.of_mul_eq_one (9269 : ZMod 18539)
      decide
    · apply IsUnit.of_mul_eq_one (923 : ZMod 18539)
      decide
    · apply IsUnit.of_mul_eq_one (8637 : ZMod 18539)
      decide
    · apply IsUnit.of_mul_eq_one (8127 : ZMod 18539)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_18541 : Nat.Prime 18541 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 18541 18540 1 6 [2, 2, 3, 3, 5, 103]
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
    · apply IsUnit.of_mul_eq_one (9270 : ZMod 18541)
      decide
    · apply IsUnit.of_mul_eq_one (7091 : ZMod 18541)
      decide
    · apply IsUnit.of_mul_eq_one (6191 : ZMod 18541)
      decide
    · apply IsUnit.of_mul_eq_one (13871 : ZMod 18541)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_18553 : Nat.Prime 18553 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 18553 18552 1 5 [2, 2, 2, 3, 773]
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
    · apply IsUnit.of_mul_eq_one (9276 : ZMod 18553)
      decide
    · apply IsUnit.of_mul_eq_one (9805 : ZMod 18553)
      decide
    · apply IsUnit.of_mul_eq_one (1722 : ZMod 18553)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_18583 : Nat.Prime 18583 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 18583 18582 1 3 [2, 3, 19, 163]
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
    · apply IsUnit.of_mul_eq_one (9291 : ZMod 18583)
      decide
    · apply IsUnit.of_mul_eq_one (8204 : ZMod 18583)
      decide
    · apply IsUnit.of_mul_eq_one (15045 : ZMod 18583)
      decide
    · apply IsUnit.of_mul_eq_one (14429 : ZMod 18583)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_18587 : Nat.Prime 18587 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 18587 18586 1 2 [2, 9293]
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
    · apply IsUnit.of_mul_eq_one (9293 : ZMod 18587)
      decide
    · apply IsUnit.of_mul_eq_one (6196 : ZMod 18587)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_18593 : Nat.Prime 18593 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 18593 18592 1 3 [2, 2, 2, 2, 2, 7, 83]
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
    · apply IsUnit.of_mul_eq_one (9296 : ZMod 18593)
      decide
    · apply IsUnit.of_mul_eq_one (10267 : ZMod 18593)
      decide
    · apply IsUnit.of_mul_eq_one (2167 : ZMod 18593)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_18617 : Nat.Prime 18617 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 18617 18616 1 3 [2, 2, 2, 13, 179]
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
    · apply IsUnit.of_mul_eq_one (9308 : ZMod 18617)
      decide
    · apply IsUnit.of_mul_eq_one (13446 : ZMod 18617)
      decide
    · apply IsUnit.of_mul_eq_one (2884 : ZMod 18617)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_18637 : Nat.Prime 18637 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 18637 18636 1 2 [2, 2, 3, 1553]
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
    · apply IsUnit.of_mul_eq_one (9318 : ZMod 18637)
      decide
    · apply IsUnit.of_mul_eq_one (12886 : ZMod 18637)
      decide
    · apply IsUnit.of_mul_eq_one (15301 : ZMod 18637)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_18661 : Nat.Prime 18661 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 18661 18660 1 10 [2, 2, 3, 5, 311]
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
    · apply IsUnit.of_mul_eq_one (9330 : ZMod 18661)
      decide
    · apply IsUnit.of_mul_eq_one (7085 : ZMod 18661)
      decide
    · apply IsUnit.of_mul_eq_one (9560 : ZMod 18661)
      decide
    · apply IsUnit.of_mul_eq_one (10989 : ZMod 18661)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_18671 : Nat.Prime 18671 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 18671 18670 1 7 [2, 5, 1867]
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
    · apply IsUnit.of_mul_eq_one (9335 : ZMod 18671)
      decide
    · apply IsUnit.of_mul_eq_one (4460 : ZMod 18671)
      decide
    · apply IsUnit.of_mul_eq_one (10756 : ZMod 18671)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_18679 : Nat.Prime 18679 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 18679 18678 1 6 [2, 3, 11, 283]
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
    · apply IsUnit.of_mul_eq_one (9339 : ZMod 18679)
      decide
    · apply IsUnit.of_mul_eq_one (11150 : ZMod 18679)
      decide
    · apply IsUnit.of_mul_eq_one (11491 : ZMod 18679)
      decide
    · apply IsUnit.of_mul_eq_one (14067 : ZMod 18679)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_18691 : Nat.Prime 18691 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 18691 18690 1 3 [2, 3, 5, 7, 89]
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
    · apply IsUnit.of_mul_eq_one (9345 : ZMod 18691)
      decide
    · apply IsUnit.of_mul_eq_one (5931 : ZMod 18691)
      decide
    · apply IsUnit.of_mul_eq_one (2968 : ZMod 18691)
      decide
    · apply IsUnit.of_mul_eq_one (5439 : ZMod 18691)
      decide
    · apply IsUnit.of_mul_eq_one (14194 : ZMod 18691)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_18701 : Nat.Prime 18701 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 18701 18700 1 2 [2, 2, 5, 5, 11, 17]
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
    · apply IsUnit.of_mul_eq_one (9350 : ZMod 18701)
      decide
    · apply IsUnit.of_mul_eq_one (11237 : ZMod 18701)
      decide
    · apply IsUnit.of_mul_eq_one (18381 : ZMod 18701)
      decide
    · apply IsUnit.of_mul_eq_one (16714 : ZMod 18701)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_18713 : Nat.Prime 18713 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 18713 18712 1 3 [2, 2, 2, 2339]
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
    · apply IsUnit.of_mul_eq_one (9356 : ZMod 18713)
      decide
    · apply IsUnit.of_mul_eq_one (5999 : ZMod 18713)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_18719 : Nat.Prime 18719 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 18719 18718 1 7 [2, 7, 7, 191]
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
    · apply IsUnit.of_mul_eq_one (9359 : ZMod 18719)
      decide
    · apply IsUnit.of_mul_eq_one (6223 : ZMod 18719)
      decide
    · apply IsUnit.of_mul_eq_one (5581 : ZMod 18719)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_18731 : Nat.Prime 18731 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 18731 18730 1 2 [2, 5, 1873]
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
    · apply IsUnit.of_mul_eq_one (9365 : ZMod 18731)
      decide
    · apply IsUnit.of_mul_eq_one (17677 : ZMod 18731)
      decide
    · apply IsUnit.of_mul_eq_one (17431 : ZMod 18731)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_18743 : Nat.Prime 18743 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 18743 18742 1 5 [2, 9371]
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
    · apply IsUnit.of_mul_eq_one (9371 : ZMod 18743)
      decide
    · apply IsUnit.of_mul_eq_one (781 : ZMod 18743)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_18749 : Nat.Prime 18749 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 18749 18748 1 2 [2, 2, 43, 109]
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
    · apply IsUnit.of_mul_eq_one (9374 : ZMod 18749)
      decide
    · apply IsUnit.of_mul_eq_one (3262 : ZMod 18749)
      decide
    · apply IsUnit.of_mul_eq_one (12720 : ZMod 18749)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_18757 : Nat.Prime 18757 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 18757 18756 1 2 [2, 2, 3, 3, 521]
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
    · apply IsUnit.of_mul_eq_one (9378 : ZMod 18757)
      decide
    · apply IsUnit.of_mul_eq_one (7613 : ZMod 18757)
      decide
    · apply IsUnit.of_mul_eq_one (1858 : ZMod 18757)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_18773 : Nat.Prime 18773 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 18773 18772 1 2 [2, 2, 13, 19, 19]
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
    · apply IsUnit.of_mul_eq_one (9386 : ZMod 18773)
      decide
    · apply IsUnit.of_mul_eq_one (8038 : ZMod 18773)
      decide
    · apply IsUnit.of_mul_eq_one (9050 : ZMod 18773)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_18787 : Nat.Prime 18787 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 18787 18786 1 2 [2, 3, 31, 101]
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
    · apply IsUnit.of_mul_eq_one (9393 : ZMod 18787)
      decide
    · apply IsUnit.of_mul_eq_one (3527 : ZMod 18787)
      decide
    · apply IsUnit.of_mul_eq_one (9175 : ZMod 18787)
      decide
    · apply IsUnit.of_mul_eq_one (18714 : ZMod 18787)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_18793 : Nat.Prime 18793 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 18793 18792 1 5 [2, 2, 2, 3, 3, 3, 3, 29]
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
    · apply IsUnit.of_mul_eq_one (9396 : ZMod 18793)
      decide
    · apply IsUnit.of_mul_eq_one (11810 : ZMod 18793)
      decide
    · apply IsUnit.of_mul_eq_one (4890 : ZMod 18793)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_18797 : Nat.Prime 18797 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 18797 18796 1 3 [2, 2, 37, 127]
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
    · apply IsUnit.of_mul_eq_one (9398 : ZMod 18797)
      decide
    · apply IsUnit.of_mul_eq_one (17289 : ZMod 18797)
      decide
    · apply IsUnit.of_mul_eq_one (17111 : ZMod 18797)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_18803 : Nat.Prime 18803 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 18803 18802 1 5 [2, 7, 17, 79]
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
    · apply IsUnit.of_mul_eq_one (9401 : ZMod 18803)
      decide
    · apply IsUnit.of_mul_eq_one (13310 : ZMod 18803)
      decide
    · apply IsUnit.of_mul_eq_one (12984 : ZMod 18803)
      decide
    · apply IsUnit.of_mul_eq_one (12069 : ZMod 18803)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_19843 : Nat.Prime 19843 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 19843 19842 1 19 [2, 3, 3307]
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
    · apply IsUnit.of_mul_eq_one (9921 : ZMod 19843)
      decide
    · apply IsUnit.of_mul_eq_one (15803 : ZMod 19843)
      decide
    · apply IsUnit.of_mul_eq_one (15065 : ZMod 19843)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_19853 : Nat.Prime 19853 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 19853 19852 1 2 [2, 2, 7, 709]
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
    · apply IsUnit.of_mul_eq_one (9926 : ZMod 19853)
      decide
    · apply IsUnit.of_mul_eq_one (9158 : ZMod 19853)
      decide
    · apply IsUnit.of_mul_eq_one (124 : ZMod 19853)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_19861 : Nat.Prime 19861 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 19861 19860 1 11 [2, 2, 3, 5, 331]
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
    · apply IsUnit.of_mul_eq_one (9930 : ZMod 19861)
      decide
    · apply IsUnit.of_mul_eq_one (11143 : ZMod 19861)
      decide
    · apply IsUnit.of_mul_eq_one (6913 : ZMod 19861)
      decide
    · apply IsUnit.of_mul_eq_one (2000 : ZMod 19861)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_19867 : Nat.Prime 19867 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 19867 19866 1 2 [2, 3, 7, 11, 43]
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
    · apply IsUnit.of_mul_eq_one (9933 : ZMod 19867)
      decide
    · apply IsUnit.of_mul_eq_one (14776 : ZMod 19867)
      decide
    · apply IsUnit.of_mul_eq_one (5342 : ZMod 19867)
      decide
    · apply IsUnit.of_mul_eq_one (19534 : ZMod 19867)
      decide
    · apply IsUnit.of_mul_eq_one (12416 : ZMod 19867)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_19889 : Nat.Prime 19889 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 19889 19888 1 3 [2, 2, 2, 2, 11, 113]
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
    · apply IsUnit.of_mul_eq_one (9944 : ZMod 19889)
      decide
    · apply IsUnit.of_mul_eq_one (1630 : ZMod 19889)
      decide
    · apply IsUnit.of_mul_eq_one (13974 : ZMod 19889)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_19891 : Nat.Prime 19891 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 19891 19890 1 2 [2, 3, 3, 5, 13, 17]
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
    · apply IsUnit.of_mul_eq_one (9945 : ZMod 19891)
      decide
    · apply IsUnit.of_mul_eq_one (7172 : ZMod 19891)
      decide
    · apply IsUnit.of_mul_eq_one (19139 : ZMod 19891)
      decide
    · apply IsUnit.of_mul_eq_one (11976 : ZMod 19891)
      decide
    · apply IsUnit.of_mul_eq_one (2694 : ZMod 19891)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_19913 : Nat.Prime 19913 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 19913 19912 1 3 [2, 2, 2, 19, 131]
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
    · apply IsUnit.of_mul_eq_one (9956 : ZMod 19913)
      decide
    · apply IsUnit.of_mul_eq_one (15115 : ZMod 19913)
      decide
    · apply IsUnit.of_mul_eq_one (8511 : ZMod 19913)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_19919 : Nat.Prime 19919 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 19919 19918 1 7 [2, 23, 433]
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
    · apply IsUnit.of_mul_eq_one (9959 : ZMod 19919)
      decide
    · apply IsUnit.of_mul_eq_one (16088 : ZMod 19919)
      decide
    · apply IsUnit.of_mul_eq_one (14882 : ZMod 19919)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_19927 : Nat.Prime 19927 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 19927 19926 1 6 [2, 3, 3, 3, 3, 3, 41]
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
    · apply IsUnit.of_mul_eq_one (9963 : ZMod 19927)
      decide
    · apply IsUnit.of_mul_eq_one (81 : ZMod 19927)
      decide
    · apply IsUnit.of_mul_eq_one (3982 : ZMod 19927)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_19937 : Nat.Prime 19937 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 19937 19936 1 3 [2, 2, 2, 2, 2, 7, 89]
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
    · apply IsUnit.of_mul_eq_one (9968 : ZMod 19937)
      decide
    · apply IsUnit.of_mul_eq_one (11232 : ZMod 19937)
      decide
    · apply IsUnit.of_mul_eq_one (12798 : ZMod 19937)
      decide
  · norm_num
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_18959_19936_part12 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_19930 (p := 19841) (q := 19843) (by exact lowPrime_19843) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_19930 (p := 19843) (q := 19853) (by exact lowPrime_19853) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_19930 (p := 19853) (q := 19861) (by exact lowPrime_19861) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_19930 (p := 19861) (q := 19867) (by exact lowPrime_19867) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_19930 (p := 19867) (q := 19889) (by exact lowPrime_19889) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_19930 (p := 19889) (q := 19891) (by exact lowPrime_19891) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_19930 (p := 19891) (q := 19913) (by exact lowPrime_19913) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_19930 (p := 19913) (q := 19919) (by exact lowPrime_19919) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_18959_19936_part12_chain :
    DusartPrimeRowsChain 19841 19918 dusartPrimeRows_18959_19936_part12 := by
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
def dusartPrimeRows_18959_19936_part13 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_19930 (p := 19919) (q := 19927) (by exact lowPrime_19927) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_19930 (p := 19927) (q := 19937) (by exact lowPrime_19937) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_18959_19936_part13_chain :
    DusartPrimeRowsChain 19919 19936 dusartPrimeRows_18959_19936_part13 := by
  apply DusartPrimeRowsChain.cons
  · norm_num [dusartPrimeRow_of_explicit_19930]
  · norm_num [dusartPrimeRow_of_explicit_19930]
  · apply DusartPrimeRowsChain.cons
    · norm_num [dusartPrimeRow_of_explicit_19930]
    · norm_num [dusartPrimeRow_of_explicit_19930]
    · apply DusartPrimeRowsChain.empty
      norm_num [dusartPrimeRow_of_explicit_19930, dusartPrimeRow_of_explicit_right]

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_18041_18958_part01 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_18958 (p := 18041) (q := 18043) (by exact lowPrime_18043) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18958 (p := 18043) (q := 18047) (by exact lowPrime_18047) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18958 (p := 18047) (q := 18049) (by exact lowPrime_18049) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18958 (p := 18049) (q := 18059) (by exact lowPrime_18059) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18958 (p := 18059) (q := 18061) (by exact lowPrime_18061) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18958 (p := 18061) (q := 18077) (by exact lowPrime_18077) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18958 (p := 18077) (q := 18089) (by exact lowPrime_18089) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18958 (p := 18089) (q := 18097) (by exact lowPrime_18097) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_18041_18958_part01_chain :
    DusartPrimeRowsChain 18041 18096 dusartPrimeRows_18041_18958_part01 := by
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
def dusartPrimeRows_18041_18958_part02 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_18958 (p := 18097) (q := 18119) (by exact lowPrime_18119) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18958 (p := 18119) (q := 18121) (by exact lowPrime_18121) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18958 (p := 18121) (q := 18127) (by exact lowPrime_18127) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18958 (p := 18127) (q := 18131) (by exact lowPrime_18131) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18958 (p := 18131) (q := 18133) (by exact lowPrime_18133) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18958 (p := 18133) (q := 18143) (by exact lowPrime_18143) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18958 (p := 18143) (q := 18149) (by exact lowPrime_18149) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18958 (p := 18149) (q := 18169) (by exact lowPrime_18169) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_18041_18958_part02_chain :
    DusartPrimeRowsChain 18097 18168 dusartPrimeRows_18041_18958_part02 := by
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
def dusartPrimeRows_18041_18958_part03 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_18958 (p := 18169) (q := 18181) (by exact lowPrime_18181) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18958 (p := 18181) (q := 18191) (by exact lowPrime_18191) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18958 (p := 18191) (q := 18199) (by exact lowPrime_18199) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18958 (p := 18199) (q := 18211) (by exact lowPrime_18211) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18958 (p := 18211) (q := 18217) (by exact lowPrime_18217) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18958 (p := 18217) (q := 18223) (by exact lowPrime_18223) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18958 (p := 18223) (q := 18229) (by exact lowPrime_18229) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18958 (p := 18229) (q := 18233) (by exact lowPrime_18233) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_18041_18958_part03_chain :
    DusartPrimeRowsChain 18169 18232 dusartPrimeRows_18041_18958_part03 := by
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
def dusartPrimeRows_18041_18958_part04 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_18958 (p := 18233) (q := 18251) (by exact lowPrime_18251) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18958 (p := 18251) (q := 18253) (by exact lowPrime_18253) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18958 (p := 18253) (q := 18257) (by exact lowPrime_18257) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18958 (p := 18257) (q := 18269) (by exact lowPrime_18269) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18958 (p := 18269) (q := 18287) (by exact lowPrime_18287) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18958 (p := 18287) (q := 18289) (by exact lowPrime_18289) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18958 (p := 18289) (q := 18301) (by exact lowPrime_18301) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18958 (p := 18301) (q := 18307) (by exact lowPrime_18307) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_18041_18958_part04_chain :
    DusartPrimeRowsChain 18233 18306 dusartPrimeRows_18041_18958_part04 := by
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
def dusartPrimeRows_18041_18958_part05 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_18958 (p := 18307) (q := 18311) (by exact lowPrime_18311) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18958 (p := 18311) (q := 18313) (by exact lowPrime_18313) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18958 (p := 18313) (q := 18329) (by exact lowPrime_18329) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18958 (p := 18329) (q := 18341) (by exact lowPrime_18341) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18958 (p := 18341) (q := 18353) (by exact lowPrime_18353) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18958 (p := 18353) (q := 18367) (by exact lowPrime_18367) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18958 (p := 18367) (q := 18371) (by exact lowPrime_18371) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18958 (p := 18371) (q := 18379) (by exact lowPrime_18379) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_18041_18958_part05_chain :
    DusartPrimeRowsChain 18307 18378 dusartPrimeRows_18041_18958_part05 := by
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
def dusartPrimeRows_18041_18958_part06 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_18958 (p := 18379) (q := 18397) (by exact lowPrime_18397) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18958 (p := 18397) (q := 18401) (by exact lowPrime_18401) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18958 (p := 18401) (q := 18413) (by exact lowPrime_18413) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18958 (p := 18413) (q := 18427) (by exact lowPrime_18427) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18958 (p := 18427) (q := 18433) (by exact lowPrime_18433) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18958 (p := 18433) (q := 18439) (by exact lowPrime_18439) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18958 (p := 18439) (q := 18443) (by exact lowPrime_18443) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18958 (p := 18443) (q := 18451) (by exact lowPrime_18451) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_18041_18958_part06_chain :
    DusartPrimeRowsChain 18379 18450 dusartPrimeRows_18041_18958_part06 := by
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
def dusartPrimeRows_18041_18958_part07 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_18958 (p := 18451) (q := 18457) (by exact lowPrime_18457) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18958 (p := 18457) (q := 18461) (by exact lowPrime_18461) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18958 (p := 18461) (q := 18481) (by exact lowPrime_18481) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18958 (p := 18481) (q := 18493) (by exact lowPrime_18493) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18958 (p := 18493) (q := 18503) (by exact lowPrime_18503) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18958 (p := 18503) (q := 18517) (by exact lowPrime_18517) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18958 (p := 18517) (q := 18521) (by exact lowPrime_18521) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18958 (p := 18521) (q := 18523) (by exact lowPrime_18523) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_18041_18958_part07_chain :
    DusartPrimeRowsChain 18451 18522 dusartPrimeRows_18041_18958_part07 := by
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
def dusartPrimeRows_18041_18958_part08 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_18958 (p := 18523) (q := 18539) (by exact lowPrime_18539) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18958 (p := 18539) (q := 18541) (by exact lowPrime_18541) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18958 (p := 18541) (q := 18553) (by exact lowPrime_18553) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18958 (p := 18553) (q := 18583) (by exact lowPrime_18583) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18958 (p := 18583) (q := 18587) (by exact lowPrime_18587) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18958 (p := 18587) (q := 18593) (by exact lowPrime_18593) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18958 (p := 18593) (q := 18617) (by exact lowPrime_18617) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18958 (p := 18617) (q := 18637) (by exact lowPrime_18637) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_18041_18958_part08_chain :
    DusartPrimeRowsChain 18523 18636 dusartPrimeRows_18041_18958_part08 := by
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
def dusartPrimeRows_18041_18958_part09 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_18958 (p := 18637) (q := 18661) (by exact lowPrime_18661) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18958 (p := 18661) (q := 18671) (by exact lowPrime_18671) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18958 (p := 18671) (q := 18679) (by exact lowPrime_18679) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18958 (p := 18679) (q := 18691) (by exact lowPrime_18691) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18958 (p := 18691) (q := 18701) (by exact lowPrime_18701) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18958 (p := 18701) (q := 18713) (by exact lowPrime_18713) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18958 (p := 18713) (q := 18719) (by exact lowPrime_18719) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18958 (p := 18719) (q := 18731) (by exact lowPrime_18731) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_18041_18958_part09_chain :
    DusartPrimeRowsChain 18637 18730 dusartPrimeRows_18041_18958_part09 := by
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
def dusartPrimeRows_18041_18958_part10 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_18958 (p := 18731) (q := 18743) (by exact lowPrime_18743) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18958 (p := 18743) (q := 18749) (by exact lowPrime_18749) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18958 (p := 18749) (q := 18757) (by exact lowPrime_18757) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18958 (p := 18757) (q := 18773) (by exact lowPrime_18773) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18958 (p := 18773) (q := 18787) (by exact lowPrime_18787) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18958 (p := 18787) (q := 18793) (by exact lowPrime_18793) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18958 (p := 18793) (q := 18797) (by exact lowPrime_18797) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18958 (p := 18797) (q := 18803) (by exact lowPrime_18803) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_18041_18958_part10_chain :
    DusartPrimeRowsChain 18731 18802 dusartPrimeRows_18041_18958_part10 := by
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
