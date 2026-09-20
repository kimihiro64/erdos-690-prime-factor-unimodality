import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowBase

set_option autoImplicit false
set_option maxRecDepth 1000000

/-! # Lower finite Dusart prefix chunk 07 -/

namespace PrimeFactorUnimodality

noncomputable section
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_8117 : Nat.Prime 8117 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 8117 8116 1 2 [2, 2, 2029]
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
    · apply IsUnit.of_mul_eq_one (4058 : ZMod 8117)
      decide
    · apply IsUnit.of_mul_eq_one (3788 : ZMod 8117)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_8123 : Nat.Prime 8123 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 8123 8122 1 2 [2, 31, 131]
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
    · apply IsUnit.of_mul_eq_one (4061 : ZMod 8123)
      decide
    · apply IsUnit.of_mul_eq_one (3866 : ZMod 8123)
      decide
    · apply IsUnit.of_mul_eq_one (7709 : ZMod 8123)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_8147 : Nat.Prime 8147 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 8147 8146 1 2 [2, 4073]
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
    · apply IsUnit.of_mul_eq_one (4073 : ZMod 8147)
      decide
    · apply IsUnit.of_mul_eq_one (2716 : ZMod 8147)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_8161 : Nat.Prime 8161 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 8161 8160 1 7 [2, 2, 2, 2, 2, 3, 5, 17]
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
    · apply IsUnit.of_mul_eq_one (4080 : ZMod 8161)
      decide
    · apply IsUnit.of_mul_eq_one (6408 : ZMod 8161)
      decide
    · apply IsUnit.of_mul_eq_one (2231 : ZMod 8161)
      decide
    · apply IsUnit.of_mul_eq_one (2310 : ZMod 8161)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_8167 : Nat.Prime 8167 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 8167 8166 1 3 [2, 3, 1361]
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
    · apply IsUnit.of_mul_eq_one (4083 : ZMod 8167)
      decide
    · apply IsUnit.of_mul_eq_one (1691 : ZMod 8167)
      decide
    · apply IsUnit.of_mul_eq_one (7191 : ZMod 8167)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_8171 : Nat.Prime 8171 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 8171 8170 1 2 [2, 5, 19, 43]
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
    · apply IsUnit.of_mul_eq_one (4085 : ZMod 8171)
      decide
    · apply IsUnit.of_mul_eq_one (5060 : ZMod 8171)
      decide
    · apply IsUnit.of_mul_eq_one (383 : ZMod 8171)
      decide
    · apply IsUnit.of_mul_eq_one (7581 : ZMod 8171)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_8179 : Nat.Prime 8179 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 8179 8178 1 2 [2, 3, 29, 47]
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
    · apply IsUnit.of_mul_eq_one (4089 : ZMod 8179)
      decide
    · apply IsUnit.of_mul_eq_one (7813 : ZMod 8179)
      decide
    · apply IsUnit.of_mul_eq_one (6725 : ZMod 8179)
      decide
    · apply IsUnit.of_mul_eq_one (3326 : ZMod 8179)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_8191 : Nat.Prime 8191 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 8191 8190 1 17 [2, 3, 3, 5, 7, 13]
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
    · apply IsUnit.of_mul_eq_one (4095 : ZMod 8191)
      decide
    · apply IsUnit.of_mul_eq_one (2760 : ZMod 8191)
      decide
    · apply IsUnit.of_mul_eq_one (2653 : ZMod 8191)
      decide
    · apply IsUnit.of_mul_eq_one (3806 : ZMod 8191)
      decide
    · apply IsUnit.of_mul_eq_one (7021 : ZMod 8191)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_8209 : Nat.Prime 8209 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 8209 8208 1 7 [2, 2, 2, 2, 3, 3, 3, 19]
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
    · apply IsUnit.of_mul_eq_one (4104 : ZMod 8209)
      decide
    · apply IsUnit.of_mul_eq_one (7120 : ZMod 8209)
      decide
    · apply IsUnit.of_mul_eq_one (3087 : ZMod 8209)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_8219 : Nat.Prime 8219 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 8219 8218 1 2 [2, 7, 587]
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
    · apply IsUnit.of_mul_eq_one (4109 : ZMod 8219)
      decide
    · apply IsUnit.of_mul_eq_one (261 : ZMod 8219)
      decide
    · apply IsUnit.of_mul_eq_one (5828 : ZMod 8219)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_8221 : Nat.Prime 8221 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 8221 8220 1 2 [2, 2, 3, 5, 137]
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
    · apply IsUnit.of_mul_eq_one (4110 : ZMod 8221)
      decide
    · apply IsUnit.of_mul_eq_one (8082 : ZMod 8221)
      decide
    · apply IsUnit.of_mul_eq_one (1189 : ZMod 8221)
      decide
    · apply IsUnit.of_mul_eq_one (7376 : ZMod 8221)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_8231 : Nat.Prime 8231 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 8231 8230 1 11 [2, 5, 823]
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
    · apply IsUnit.of_mul_eq_one (4115 : ZMod 8231)
      decide
    · apply IsUnit.of_mul_eq_one (2645 : ZMod 8231)
      decide
    · apply IsUnit.of_mul_eq_one (1546 : ZMod 8231)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_8233 : Nat.Prime 8233 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 8233 8232 1 10 [2, 2, 2, 3, 7, 7, 7]
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
    · apply IsUnit.of_mul_eq_one (4116 : ZMod 8233)
      decide
    · apply IsUnit.of_mul_eq_one (1873 : ZMod 8233)
      decide
    · apply IsUnit.of_mul_eq_one (7943 : ZMod 8233)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_8237 : Nat.Prime 8237 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 8237 8236 1 2 [2, 2, 29, 71]
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
    · apply IsUnit.of_mul_eq_one (4118 : ZMod 8237)
      decide
    · apply IsUnit.of_mul_eq_one (6337 : ZMod 8237)
      decide
    · apply IsUnit.of_mul_eq_one (5515 : ZMod 8237)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_8243 : Nat.Prime 8243 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 8243 8242 1 2 [2, 13, 317]
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
    · apply IsUnit.of_mul_eq_one (4121 : ZMod 8243)
      decide
    · apply IsUnit.of_mul_eq_one (4637 : ZMod 8243)
      decide
    · apply IsUnit.of_mul_eq_one (1563 : ZMod 8243)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_8263 : Nat.Prime 8263 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 8263 8262 1 3 [2, 3, 3, 3, 3, 3, 17]
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
    · apply IsUnit.of_mul_eq_one (4131 : ZMod 8263)
      decide
    · apply IsUnit.of_mul_eq_one (5428 : ZMod 8263)
      decide
    · apply IsUnit.of_mul_eq_one (7741 : ZMod 8263)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_8269 : Nat.Prime 8269 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 8269 8268 1 2 [2, 2, 3, 13, 53]
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
    · apply IsUnit.of_mul_eq_one (4134 : ZMod 8269)
      decide
    · apply IsUnit.of_mul_eq_one (52 : ZMod 8269)
      decide
    · apply IsUnit.of_mul_eq_one (5435 : ZMod 8269)
      decide
    · apply IsUnit.of_mul_eq_one (1260 : ZMod 8269)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_8273 : Nat.Prime 8273 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 8273 8272 1 3 [2, 2, 2, 2, 11, 47]
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
    · apply IsUnit.of_mul_eq_one (4136 : ZMod 8273)
      decide
    · apply IsUnit.of_mul_eq_one (3762 : ZMod 8273)
      decide
    · apply IsUnit.of_mul_eq_one (6509 : ZMod 8273)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_8287 : Nat.Prime 8287 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 8287 8286 1 3 [2, 3, 1381]
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
    · apply IsUnit.of_mul_eq_one (4143 : ZMod 8287)
      decide
    · apply IsUnit.of_mul_eq_one (8097 : ZMod 8287)
      decide
    · apply IsUnit.of_mul_eq_one (6386 : ZMod 8287)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_8291 : Nat.Prime 8291 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 8291 8290 1 2 [2, 5, 829]
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
    · apply IsUnit.of_mul_eq_one (4145 : ZMod 8291)
      decide
    · apply IsUnit.of_mul_eq_one (7547 : ZMod 8291)
      decide
    · apply IsUnit.of_mul_eq_one (5114 : ZMod 8291)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_8293 : Nat.Prime 8293 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 8293 8292 1 2 [2, 2, 3, 691]
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
    · apply IsUnit.of_mul_eq_one (4146 : ZMod 8293)
      decide
    · apply IsUnit.of_mul_eq_one (683 : ZMod 8293)
      decide
    · apply IsUnit.of_mul_eq_one (5636 : ZMod 8293)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_8297 : Nat.Prime 8297 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 8297 8296 1 3 [2, 2, 2, 17, 61]
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
    · apply IsUnit.of_mul_eq_one (4148 : ZMod 8297)
      decide
    · apply IsUnit.of_mul_eq_one (87 : ZMod 8297)
      decide
    · apply IsUnit.of_mul_eq_one (1311 : ZMod 8297)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_8311 : Nat.Prime 8311 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 8311 8310 1 3 [2, 3, 5, 277]
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
    · apply IsUnit.of_mul_eq_one (4155 : ZMod 8311)
      decide
    · apply IsUnit.of_mul_eq_one (3192 : ZMod 8311)
      decide
    · apply IsUnit.of_mul_eq_one (5690 : ZMod 8311)
      decide
    · apply IsUnit.of_mul_eq_one (4836 : ZMod 8311)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_8317 : Nat.Prime 8317 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 8317 8316 1 6 [2, 2, 3, 3, 3, 7, 11]
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
    · apply IsUnit.of_mul_eq_one (4158 : ZMod 8317)
      decide
    · apply IsUnit.of_mul_eq_one (2343 : ZMod 8317)
      decide
    · apply IsUnit.of_mul_eq_one (2224 : ZMod 8317)
      decide
    · apply IsUnit.of_mul_eq_one (5547 : ZMod 8317)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_8329 : Nat.Prime 8329 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 8329 8328 1 7 [2, 2, 2, 3, 347]
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
    · apply IsUnit.of_mul_eq_one (4164 : ZMod 8329)
      decide
    · apply IsUnit.of_mul_eq_one (5903 : ZMod 8329)
      decide
    · apply IsUnit.of_mul_eq_one (4312 : ZMod 8329)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_8353 : Nat.Prime 8353 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 8353 8352 1 5 [2, 2, 2, 2, 2, 3, 3, 29]
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
    · apply IsUnit.of_mul_eq_one (4176 : ZMod 8353)
      decide
    · apply IsUnit.of_mul_eq_one (2205 : ZMod 8353)
      decide
    · apply IsUnit.of_mul_eq_one (8320 : ZMod 8353)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_8363 : Nat.Prime 8363 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 8363 8362 1 2 [2, 37, 113]
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
    · apply IsUnit.of_mul_eq_one (4181 : ZMod 8363)
      decide
    · apply IsUnit.of_mul_eq_one (6983 : ZMod 8363)
      decide
    · apply IsUnit.of_mul_eq_one (7763 : ZMod 8363)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_8369 : Nat.Prime 8369 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 8369 8368 1 3 [2, 2, 2, 2, 523]
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
    · apply IsUnit.of_mul_eq_one (4184 : ZMod 8369)
      decide
    · apply IsUnit.of_mul_eq_one (2080 : ZMod 8369)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_8377 : Nat.Prime 8377 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 8377 8376 1 5 [2, 2, 2, 3, 349]
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
    · apply IsUnit.of_mul_eq_one (4188 : ZMod 8377)
      decide
    · apply IsUnit.of_mul_eq_one (5313 : ZMod 8377)
      decide
    · apply IsUnit.of_mul_eq_one (2759 : ZMod 8377)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_8387 : Nat.Prime 8387 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 8387 8386 1 2 [2, 7, 599]
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
    · apply IsUnit.of_mul_eq_one (4193 : ZMod 8387)
      decide
    · apply IsUnit.of_mul_eq_one (6456 : ZMod 8387)
      decide
    · apply IsUnit.of_mul_eq_one (429 : ZMod 8387)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_8389 : Nat.Prime 8389 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 8389 8388 1 6 [2, 2, 3, 3, 233]
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
    · apply IsUnit.of_mul_eq_one (4194 : ZMod 8389)
      decide
    · apply IsUnit.of_mul_eq_one (8158 : ZMod 8389)
      decide
    · apply IsUnit.of_mul_eq_one (1599 : ZMod 8389)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_8419 : Nat.Prime 8419 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 8419 8418 1 3 [2, 3, 23, 61]
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
    · apply IsUnit.of_mul_eq_one (4209 : ZMod 8419)
      decide
    · apply IsUnit.of_mul_eq_one (2152 : ZMod 8419)
      decide
    · apply IsUnit.of_mul_eq_one (5744 : ZMod 8419)
      decide
    · apply IsUnit.of_mul_eq_one (8029 : ZMod 8419)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_8423 : Nat.Prime 8423 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 8423 8422 1 5 [2, 4211]
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
    · apply IsUnit.of_mul_eq_one (4211 : ZMod 8423)
      decide
    · apply IsUnit.of_mul_eq_one (351 : ZMod 8423)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_8429 : Nat.Prime 8429 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 8429 8428 1 2 [2, 2, 7, 7, 43]
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
    · apply IsUnit.of_mul_eq_one (4214 : ZMod 8429)
      decide
    · apply IsUnit.of_mul_eq_one (5886 : ZMod 8429)
      decide
    · apply IsUnit.of_mul_eq_one (6920 : ZMod 8429)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_8431 : Nat.Prime 8431 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 8431 8430 1 3 [2, 3, 5, 281]
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
    · apply IsUnit.of_mul_eq_one (4215 : ZMod 8431)
      decide
    · apply IsUnit.of_mul_eq_one (6336 : ZMod 8431)
      decide
    · apply IsUnit.of_mul_eq_one (876 : ZMod 8431)
      decide
    · apply IsUnit.of_mul_eq_one (1436 : ZMod 8431)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_8443 : Nat.Prime 8443 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 8443 8442 1 2 [2, 3, 3, 7, 67]
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
    · apply IsUnit.of_mul_eq_one (4221 : ZMod 8443)
      decide
    · apply IsUnit.of_mul_eq_one (5283 : ZMod 8443)
      decide
    · apply IsUnit.of_mul_eq_one (1903 : ZMod 8443)
      decide
    · apply IsUnit.of_mul_eq_one (6328 : ZMod 8443)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_8447 : Nat.Prime 8447 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 8447 8446 1 5 [2, 41, 103]
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
    · apply IsUnit.of_mul_eq_one (4223 : ZMod 8447)
      decide
    · apply IsUnit.of_mul_eq_one (2321 : ZMod 8447)
      decide
    · apply IsUnit.of_mul_eq_one (8260 : ZMod 8447)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_8461 : Nat.Prime 8461 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 8461 8460 1 6 [2, 2, 3, 3, 5, 47]
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
    · apply IsUnit.of_mul_eq_one (4230 : ZMod 8461)
      decide
    · apply IsUnit.of_mul_eq_one (3412 : ZMod 8461)
      decide
    · apply IsUnit.of_mul_eq_one (5189 : ZMod 8461)
      decide
    · apply IsUnit.of_mul_eq_one (7446 : ZMod 8461)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_8467 : Nat.Prime 8467 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 8467 8466 1 2 [2, 3, 17, 83]
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
    · apply IsUnit.of_mul_eq_one (4233 : ZMod 8467)
      decide
    · apply IsUnit.of_mul_eq_one (7040 : ZMod 8467)
      decide
    · apply IsUnit.of_mul_eq_one (4751 : ZMod 8467)
      decide
    · apply IsUnit.of_mul_eq_one (5649 : ZMod 8467)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_8501 : Nat.Prime 8501 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 8501 8500 1 7 [2, 2, 5, 5, 5, 17]
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
    · apply IsUnit.of_mul_eq_one (4250 : ZMod 8501)
      decide
    · apply IsUnit.of_mul_eq_one (1505 : ZMod 8501)
      decide
    · apply IsUnit.of_mul_eq_one (789 : ZMod 8501)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_8513 : Nat.Prime 8513 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 8513 8512 1 5 [2, 2, 2, 2, 2, 2, 7, 19]
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
    · apply IsUnit.of_mul_eq_one (4256 : ZMod 8513)
      decide
    · apply IsUnit.of_mul_eq_one (7144 : ZMod 8513)
      decide
    · apply IsUnit.of_mul_eq_one (2070 : ZMod 8513)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_8521 : Nat.Prime 8521 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 8521 8520 1 13 [2, 2, 2, 3, 5, 71]
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
    · apply IsUnit.of_mul_eq_one (4260 : ZMod 8521)
      decide
    · apply IsUnit.of_mul_eq_one (2165 : ZMod 8521)
      decide
    · apply IsUnit.of_mul_eq_one (3129 : ZMod 8521)
      decide
    · apply IsUnit.of_mul_eq_one (1336 : ZMod 8521)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_8527 : Nat.Prime 8527 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 8527 8526 1 5 [2, 3, 7, 7, 29]
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
    · apply IsUnit.of_mul_eq_one (4263 : ZMod 8527)
      decide
    · apply IsUnit.of_mul_eq_one (3834 : ZMod 8527)
      decide
    · apply IsUnit.of_mul_eq_one (394 : ZMod 8527)
      decide
    · apply IsUnit.of_mul_eq_one (744 : ZMod 8527)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_8537 : Nat.Prime 8537 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 8537 8536 1 3 [2, 2, 2, 11, 97]
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
    · apply IsUnit.of_mul_eq_one (4268 : ZMod 8537)
      decide
    · apply IsUnit.of_mul_eq_one (544 : ZMod 8537)
      decide
    · apply IsUnit.of_mul_eq_one (7731 : ZMod 8537)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_8539 : Nat.Prime 8539 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 8539 8538 1 2 [2, 3, 1423]
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
    · apply IsUnit.of_mul_eq_one (4269 : ZMod 8539)
      decide
    · apply IsUnit.of_mul_eq_one (1995 : ZMod 8539)
      decide
    · apply IsUnit.of_mul_eq_one (6777 : ZMod 8539)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_8543 : Nat.Prime 8543 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 8543 8542 1 5 [2, 4271]
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
    · apply IsUnit.of_mul_eq_one (4271 : ZMod 8543)
      decide
    · apply IsUnit.of_mul_eq_one (356 : ZMod 8543)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_8563 : Nat.Prime 8563 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 8563 8562 1 2 [2, 3, 1427]
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
    · apply IsUnit.of_mul_eq_one (4281 : ZMod 8563)
      decide
    · apply IsUnit.of_mul_eq_one (4767 : ZMod 8563)
      decide
    · apply IsUnit.of_mul_eq_one (5165 : ZMod 8563)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_8573 : Nat.Prime 8573 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 8573 8572 1 2 [2, 2, 2143]
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
    · apply IsUnit.of_mul_eq_one (4286 : ZMod 8573)
      decide
    · apply IsUnit.of_mul_eq_one (7430 : ZMod 8573)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_8581 : Nat.Prime 8581 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 8581 8580 1 6 [2, 2, 3, 5, 11, 13]
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
    · apply IsUnit.of_mul_eq_one (4290 : ZMod 8581)
      decide
    · apply IsUnit.of_mul_eq_one (8439 : ZMod 8581)
      decide
    · apply IsUnit.of_mul_eq_one (8084 : ZMod 8581)
      decide
    · apply IsUnit.of_mul_eq_one (4069 : ZMod 8581)
      decide
    · apply IsUnit.of_mul_eq_one (2714 : ZMod 8581)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_8597 : Nat.Prime 8597 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 8597 8596 1 2 [2, 2, 7, 307]
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
    · apply IsUnit.of_mul_eq_one (4298 : ZMod 8597)
      decide
    · apply IsUnit.of_mul_eq_one (7660 : ZMod 8597)
      decide
    · apply IsUnit.of_mul_eq_one (8411 : ZMod 8597)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_8599 : Nat.Prime 8599 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 8599 8598 1 3 [2, 3, 1433]
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
    · apply IsUnit.of_mul_eq_one (4299 : ZMod 8599)
      decide
    · apply IsUnit.of_mul_eq_one (6134 : ZMod 8599)
      decide
    · apply IsUnit.of_mul_eq_one (5398 : ZMod 8599)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_8609 : Nat.Prime 8609 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 8609 8608 1 3 [2, 2, 2, 2, 2, 269]
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
    · apply IsUnit.of_mul_eq_one (4304 : ZMod 8609)
      decide
    · apply IsUnit.of_mul_eq_one (4780 : ZMod 8609)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_8623 : Nat.Prime 8623 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 8623 8622 1 3 [2, 3, 3, 479]
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
    · apply IsUnit.of_mul_eq_one (4311 : ZMod 8623)
      decide
    · apply IsUnit.of_mul_eq_one (5233 : ZMod 8623)
      decide
    · apply IsUnit.of_mul_eq_one (4775 : ZMod 8623)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_8627 : Nat.Prime 8627 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 8627 8626 1 2 [2, 19, 227]
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
    · apply IsUnit.of_mul_eq_one (4313 : ZMod 8627)
      decide
    · apply IsUnit.of_mul_eq_one (482 : ZMod 8627)
      decide
    · apply IsUnit.of_mul_eq_one (3929 : ZMod 8627)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_8629 : Nat.Prime 8629 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 8629 8628 1 6 [2, 2, 3, 719]
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
    · apply IsUnit.of_mul_eq_one (4314 : ZMod 8629)
      decide
    · apply IsUnit.of_mul_eq_one (4650 : ZMod 8629)
      decide
    · apply IsUnit.of_mul_eq_one (2319 : ZMod 8629)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_8641 : Nat.Prime 8641 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 8641 8640 1 17 [2, 2, 2, 2, 2, 2, 3, 3, 3, 5]
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
    · apply IsUnit.of_mul_eq_one (4320 : ZMod 8641)
      decide
    · apply IsUnit.of_mul_eq_one (6951 : ZMod 8641)
      decide
    · apply IsUnit.of_mul_eq_one (3801 : ZMod 8641)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_8647 : Nat.Prime 8647 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 8647 8646 1 3 [2, 3, 11, 131]
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
    · apply IsUnit.of_mul_eq_one (4323 : ZMod 8647)
      decide
    · apply IsUnit.of_mul_eq_one (2617 : ZMod 8647)
      decide
    · apply IsUnit.of_mul_eq_one (6748 : ZMod 8647)
      decide
    · apply IsUnit.of_mul_eq_one (2137 : ZMod 8647)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_8663 : Nat.Prime 8663 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 8663 8662 1 5 [2, 61, 71]
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
    · apply IsUnit.of_mul_eq_one (4331 : ZMod 8663)
      decide
    · apply IsUnit.of_mul_eq_one (4990 : ZMod 8663)
      decide
    · apply IsUnit.of_mul_eq_one (6368 : ZMod 8663)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_8669 : Nat.Prime 8669 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 8669 8668 1 2 [2, 2, 11, 197]
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
    · apply IsUnit.of_mul_eq_one (4334 : ZMod 8669)
      decide
    · apply IsUnit.of_mul_eq_one (4722 : ZMod 8669)
      decide
    · apply IsUnit.of_mul_eq_one (5512 : ZMod 8669)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_8677 : Nat.Prime 8677 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 8677 8676 1 2 [2, 2, 3, 3, 241]
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
    · apply IsUnit.of_mul_eq_one (4338 : ZMod 8677)
      decide
    · apply IsUnit.of_mul_eq_one (8217 : ZMod 8677)
      decide
    · apply IsUnit.of_mul_eq_one (1404 : ZMod 8677)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_8681 : Nat.Prime 8681 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 8681 8680 1 15 [2, 2, 2, 5, 7, 31]
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
    · apply IsUnit.of_mul_eq_one (4340 : ZMod 8681)
      decide
    · apply IsUnit.of_mul_eq_one (3404 : ZMod 8681)
      decide
    · apply IsUnit.of_mul_eq_one (8175 : ZMod 8681)
      decide
    · apply IsUnit.of_mul_eq_one (6082 : ZMod 8681)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_8689 : Nat.Prime 8689 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 8689 8688 1 13 [2, 2, 2, 2, 3, 181]
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
    · apply IsUnit.of_mul_eq_one (4344 : ZMod 8689)
      decide
    · apply IsUnit.of_mul_eq_one (8054 : ZMod 8689)
      decide
    · apply IsUnit.of_mul_eq_one (4782 : ZMod 8689)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_8693 : Nat.Prime 8693 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 8693 8692 1 2 [2, 2, 41, 53]
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
    · apply IsUnit.of_mul_eq_one (4346 : ZMod 8693)
      decide
    · apply IsUnit.of_mul_eq_one (4368 : ZMod 8693)
      decide
    · apply IsUnit.of_mul_eq_one (3635 : ZMod 8693)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_8699 : Nat.Prime 8699 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 8699 8698 1 2 [2, 4349]
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
    · apply IsUnit.of_mul_eq_one (4349 : ZMod 8699)
      decide
    · apply IsUnit.of_mul_eq_one (2900 : ZMod 8699)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_8707 : Nat.Prime 8707 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 8707 8706 1 5 [2, 3, 1451]
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
    · apply IsUnit.of_mul_eq_one (4353 : ZMod 8707)
      decide
    · apply IsUnit.of_mul_eq_one (804 : ZMod 8707)
      decide
    · apply IsUnit.of_mul_eq_one (2544 : ZMod 8707)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_8713 : Nat.Prime 8713 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 8713 8712 1 5 [2, 2, 2, 3, 3, 11, 11]
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
    · apply IsUnit.of_mul_eq_one (4356 : ZMod 8713)
      decide
    · apply IsUnit.of_mul_eq_one (6654 : ZMod 8713)
      decide
    · apply IsUnit.of_mul_eq_one (7898 : ZMod 8713)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_8719 : Nat.Prime 8719 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 8719 8718 1 3 [2, 3, 1453]
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
    · apply IsUnit.of_mul_eq_one (4359 : ZMod 8719)
      decide
    · apply IsUnit.of_mul_eq_one (7958 : ZMod 8719)
      decide
    · apply IsUnit.of_mul_eq_one (3078 : ZMod 8719)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_8731 : Nat.Prime 8731 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 8731 8730 1 2 [2, 3, 3, 5, 97]
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
    · apply IsUnit.of_mul_eq_one (4365 : ZMod 8731)
      decide
    · apply IsUnit.of_mul_eq_one (7511 : ZMod 8731)
      decide
    · apply IsUnit.of_mul_eq_one (4101 : ZMod 8731)
      decide
    · apply IsUnit.of_mul_eq_one (7838 : ZMod 8731)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_8737 : Nat.Prime 8737 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 8737 8736 1 5 [2, 2, 2, 2, 2, 3, 7, 13]
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
    · apply IsUnit.of_mul_eq_one (4368 : ZMod 8737)
      decide
    · apply IsUnit.of_mul_eq_one (5068 : ZMod 8737)
      decide
    · apply IsUnit.of_mul_eq_one (6289 : ZMod 8737)
      decide
    · apply IsUnit.of_mul_eq_one (1583 : ZMod 8737)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_8741 : Nat.Prime 8741 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 8741 8740 1 2 [2, 2, 5, 19, 23]
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
    · apply IsUnit.of_mul_eq_one (4370 : ZMod 8741)
      decide
    · apply IsUnit.of_mul_eq_one (7350 : ZMod 8741)
      decide
    · apply IsUnit.of_mul_eq_one (538 : ZMod 8741)
      decide
    · apply IsUnit.of_mul_eq_one (8561 : ZMod 8741)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_8747 : Nat.Prime 8747 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 8747 8746 1 2 [2, 4373]
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
    · apply IsUnit.of_mul_eq_one (4373 : ZMod 8747)
      decide
    · apply IsUnit.of_mul_eq_one (2916 : ZMod 8747)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_8753 : Nat.Prime 8753 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 8753 8752 1 3 [2, 2, 2, 2, 547]
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
    · apply IsUnit.of_mul_eq_one (4376 : ZMod 8753)
      decide
    · apply IsUnit.of_mul_eq_one (377 : ZMod 8753)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_8761 : Nat.Prime 8761 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 8761 8760 1 23 [2, 2, 2, 3, 5, 73]
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
    · apply IsUnit.of_mul_eq_one (4380 : ZMod 8761)
      decide
    · apply IsUnit.of_mul_eq_one (2342 : ZMod 8761)
      decide
    · apply IsUnit.of_mul_eq_one (2202 : ZMod 8761)
      decide
    · apply IsUnit.of_mul_eq_one (1258 : ZMod 8761)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_8779 : Nat.Prime 8779 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 8779 8778 1 11 [2, 3, 7, 11, 19]
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
    · apply IsUnit.of_mul_eq_one (4389 : ZMod 8779)
      decide
    · apply IsUnit.of_mul_eq_one (422 : ZMod 8779)
      decide
    · apply IsUnit.of_mul_eq_one (5532 : ZMod 8779)
      decide
    · apply IsUnit.of_mul_eq_one (6068 : ZMod 8779)
      decide
    · apply IsUnit.of_mul_eq_one (5351 : ZMod 8779)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_8783 : Nat.Prime 8783 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 8783 8782 1 5 [2, 4391]
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
    · apply IsUnit.of_mul_eq_one (4391 : ZMod 8783)
      decide
    · apply IsUnit.of_mul_eq_one (366 : ZMod 8783)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_8803 : Nat.Prime 8803 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 8803 8802 1 2 [2, 3, 3, 3, 163]
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
    · apply IsUnit.of_mul_eq_one (4401 : ZMod 8803)
      decide
    · apply IsUnit.of_mul_eq_one (329 : ZMod 8803)
      decide
    · apply IsUnit.of_mul_eq_one (4013 : ZMod 8803)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_8807 : Nat.Prime 8807 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 8807 8806 1 5 [2, 7, 17, 37]
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
    · apply IsUnit.of_mul_eq_one (4403 : ZMod 8807)
      decide
    · apply IsUnit.of_mul_eq_one (2565 : ZMod 8807)
      decide
    · apply IsUnit.of_mul_eq_one (1137 : ZMod 8807)
      decide
    · apply IsUnit.of_mul_eq_one (8605 : ZMod 8807)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_8819 : Nat.Prime 8819 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 8819 8818 1 2 [2, 4409]
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
    · apply IsUnit.of_mul_eq_one (4409 : ZMod 8819)
      decide
    · apply IsUnit.of_mul_eq_one (2940 : ZMod 8819)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_8821 : Nat.Prime 8821 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 8821 8820 1 2 [2, 2, 3, 3, 5, 7, 7]
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
    · apply IsUnit.of_mul_eq_one (4410 : ZMod 8821)
      decide
    · apply IsUnit.of_mul_eq_one (3752 : ZMod 8821)
      decide
    · apply IsUnit.of_mul_eq_one (5349 : ZMod 8821)
      decide
    · apply IsUnit.of_mul_eq_one (8403 : ZMod 8821)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_8831 : Nat.Prime 8831 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 8831 8830 1 7 [2, 5, 883]
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
    · apply IsUnit.of_mul_eq_one (4415 : ZMod 8831)
      decide
    · apply IsUnit.of_mul_eq_one (615 : ZMod 8831)
      decide
    · apply IsUnit.of_mul_eq_one (4744 : ZMod 8831)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_8837 : Nat.Prime 8837 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 8837 8836 1 2 [2, 2, 47, 47]
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
    · apply IsUnit.of_mul_eq_one (4418 : ZMod 8837)
      decide
    · apply IsUnit.of_mul_eq_one (8274 : ZMod 8837)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_8839 : Nat.Prime 8839 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 8839 8838 1 3 [2, 3, 3, 491]
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
    · apply IsUnit.of_mul_eq_one (4419 : ZMod 8839)
      decide
    · apply IsUnit.of_mul_eq_one (7381 : ZMod 8839)
      decide
    · apply IsUnit.of_mul_eq_one (1171 : ZMod 8839)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_8849 : Nat.Prime 8849 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 8849 8848 1 3 [2, 2, 2, 2, 7, 79]
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
    · apply IsUnit.of_mul_eq_one (4424 : ZMod 8849)
      decide
    · apply IsUnit.of_mul_eq_one (8684 : ZMod 8849)
      decide
    · apply IsUnit.of_mul_eq_one (6705 : ZMod 8849)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_8861 : Nat.Prime 8861 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 8861 8860 1 2 [2, 2, 5, 443]
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
    · apply IsUnit.of_mul_eq_one (4430 : ZMod 8861)
      decide
    · apply IsUnit.of_mul_eq_one (2126 : ZMod 8861)
      decide
    · apply IsUnit.of_mul_eq_one (2152 : ZMod 8861)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_8863 : Nat.Prime 8863 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 8863 8862 1 3 [2, 3, 7, 211]
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
    · apply IsUnit.of_mul_eq_one (4431 : ZMod 8863)
      decide
    · apply IsUnit.of_mul_eq_one (3441 : ZMod 8863)
      decide
    · apply IsUnit.of_mul_eq_one (7602 : ZMod 8863)
      decide
    · apply IsUnit.of_mul_eq_one (2442 : ZMod 8863)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_8867 : Nat.Prime 8867 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 8867 8866 1 2 [2, 11, 13, 31]
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
    · apply IsUnit.of_mul_eq_one (4433 : ZMod 8867)
      decide
    · apply IsUnit.of_mul_eq_one (3248 : ZMod 8867)
      decide
    · apply IsUnit.of_mul_eq_one (7391 : ZMod 8867)
      decide
    · apply IsUnit.of_mul_eq_one (3741 : ZMod 8867)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_8887 : Nat.Prime 8887 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 8887 8886 1 3 [2, 3, 1481]
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
    · apply IsUnit.of_mul_eq_one (4443 : ZMod 8887)
      decide
    · apply IsUnit.of_mul_eq_one (4515 : ZMod 8887)
      decide
    · apply IsUnit.of_mul_eq_one (7239 : ZMod 8887)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_8893 : Nat.Prime 8893 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 8893 8892 1 5 [2, 2, 3, 3, 13, 19]
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
    · apply IsUnit.of_mul_eq_one (4446 : ZMod 8893)
      decide
    · apply IsUnit.of_mul_eq_one (5845 : ZMod 8893)
      decide
    · apply IsUnit.of_mul_eq_one (5146 : ZMod 8893)
      decide
    · apply IsUnit.of_mul_eq_one (5017 : ZMod 8893)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_8923 : Nat.Prime 8923 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 8923 8922 1 2 [2, 3, 1487]
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
    · apply IsUnit.of_mul_eq_one (4461 : ZMod 8923)
      decide
    · apply IsUnit.of_mul_eq_one (1282 : ZMod 8923)
      decide
    · apply IsUnit.of_mul_eq_one (1558 : ZMod 8923)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_8929 : Nat.Prime 8929 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 8929 8928 1 11 [2, 2, 2, 2, 2, 3, 3, 31]
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
    · apply IsUnit.of_mul_eq_one (4464 : ZMod 8929)
      decide
    · apply IsUnit.of_mul_eq_one (7482 : ZMod 8929)
      decide
    · apply IsUnit.of_mul_eq_one (732 : ZMod 8929)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_8933 : Nat.Prime 8933 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 8933 8932 1 2 [2, 2, 7, 11, 29]
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
    · apply IsUnit.of_mul_eq_one (4466 : ZMod 8933)
      decide
    · apply IsUnit.of_mul_eq_one (6981 : ZMod 8933)
      decide
    · apply IsUnit.of_mul_eq_one (7685 : ZMod 8933)
      decide
    · apply IsUnit.of_mul_eq_one (5851 : ZMod 8933)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_8941 : Nat.Prime 8941 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 8941 8940 1 6 [2, 2, 3, 5, 149]
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
    · apply IsUnit.of_mul_eq_one (4470 : ZMod 8941)
      decide
    · apply IsUnit.of_mul_eq_one (2433 : ZMod 8941)
      decide
    · apply IsUnit.of_mul_eq_one (5138 : ZMod 8941)
      decide
    · apply IsUnit.of_mul_eq_one (3114 : ZMod 8941)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_8951 : Nat.Prime 8951 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 8951 8950 1 13 [2, 5, 5, 179]
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
    · apply IsUnit.of_mul_eq_one (4475 : ZMod 8951)
      decide
    · apply IsUnit.of_mul_eq_one (2628 : ZMod 8951)
      decide
    · apply IsUnit.of_mul_eq_one (5499 : ZMod 8951)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_8963 : Nat.Prime 8963 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 8963 8962 1 2 [2, 4481]
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
    · apply IsUnit.of_mul_eq_one (4481 : ZMod 8963)
      decide
    · apply IsUnit.of_mul_eq_one (2988 : ZMod 8963)
      decide
  · norm_num
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_8111_8520_part01 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_8518 (p := 8111) (q := 8117) (by exact lowPrime_8117) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8518 (p := 8117) (q := 8123) (by exact lowPrime_8123) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8518 (p := 8123) (q := 8147) (by exact lowPrime_8147) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8518 (p := 8147) (q := 8161) (by exact lowPrime_8161) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8518 (p := 8161) (q := 8167) (by exact lowPrime_8167) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8518 (p := 8167) (q := 8171) (by exact lowPrime_8171) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8518 (p := 8171) (q := 8179) (by exact lowPrime_8179) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8518 (p := 8179) (q := 8191) (by exact lowPrime_8191) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_8111_8520_part01_chain :
    DusartPrimeRowsChain 8111 8190 dusartPrimeRows_8111_8520_part01 := by
  apply DusartPrimeRowsChain.cons
  · norm_num [dusartPrimeRow_of_explicit_8518]
  · norm_num [dusartPrimeRow_of_explicit_8518]
  · apply DusartPrimeRowsChain.cons
    · norm_num [dusartPrimeRow_of_explicit_8518]
    · norm_num [dusartPrimeRow_of_explicit_8518]
    · apply DusartPrimeRowsChain.cons
      · norm_num [dusartPrimeRow_of_explicit_8518]
      · norm_num [dusartPrimeRow_of_explicit_8518]
      · apply DusartPrimeRowsChain.cons
        · norm_num [dusartPrimeRow_of_explicit_8518]
        · norm_num [dusartPrimeRow_of_explicit_8518]
        · apply DusartPrimeRowsChain.cons
          · norm_num [dusartPrimeRow_of_explicit_8518]
          · norm_num [dusartPrimeRow_of_explicit_8518]
          · apply DusartPrimeRowsChain.cons
            · norm_num [dusartPrimeRow_of_explicit_8518]
            · norm_num [dusartPrimeRow_of_explicit_8518]
            · apply DusartPrimeRowsChain.cons
              · norm_num [dusartPrimeRow_of_explicit_8518]
              · norm_num [dusartPrimeRow_of_explicit_8518]
              · apply DusartPrimeRowsChain.cons
                · norm_num [dusartPrimeRow_of_explicit_8518]
                · norm_num [dusartPrimeRow_of_explicit_8518]
                · apply DusartPrimeRowsChain.empty
                  norm_num [dusartPrimeRow_of_explicit_8518, dusartPrimeRow_of_explicit_right]

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_8111_8520_part02 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_8518 (p := 8191) (q := 8209) (by exact lowPrime_8209) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8518 (p := 8209) (q := 8219) (by exact lowPrime_8219) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8518 (p := 8219) (q := 8221) (by exact lowPrime_8221) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8518 (p := 8221) (q := 8231) (by exact lowPrime_8231) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8518 (p := 8231) (q := 8233) (by exact lowPrime_8233) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8518 (p := 8233) (q := 8237) (by exact lowPrime_8237) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8518 (p := 8237) (q := 8243) (by exact lowPrime_8243) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8518 (p := 8243) (q := 8263) (by exact lowPrime_8263) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_8111_8520_part02_chain :
    DusartPrimeRowsChain 8191 8262 dusartPrimeRows_8111_8520_part02 := by
  apply DusartPrimeRowsChain.cons
  · norm_num [dusartPrimeRow_of_explicit_8518]
  · norm_num [dusartPrimeRow_of_explicit_8518]
  · apply DusartPrimeRowsChain.cons
    · norm_num [dusartPrimeRow_of_explicit_8518]
    · norm_num [dusartPrimeRow_of_explicit_8518]
    · apply DusartPrimeRowsChain.cons
      · norm_num [dusartPrimeRow_of_explicit_8518]
      · norm_num [dusartPrimeRow_of_explicit_8518]
      · apply DusartPrimeRowsChain.cons
        · norm_num [dusartPrimeRow_of_explicit_8518]
        · norm_num [dusartPrimeRow_of_explicit_8518]
        · apply DusartPrimeRowsChain.cons
          · norm_num [dusartPrimeRow_of_explicit_8518]
          · norm_num [dusartPrimeRow_of_explicit_8518]
          · apply DusartPrimeRowsChain.cons
            · norm_num [dusartPrimeRow_of_explicit_8518]
            · norm_num [dusartPrimeRow_of_explicit_8518]
            · apply DusartPrimeRowsChain.cons
              · norm_num [dusartPrimeRow_of_explicit_8518]
              · norm_num [dusartPrimeRow_of_explicit_8518]
              · apply DusartPrimeRowsChain.cons
                · norm_num [dusartPrimeRow_of_explicit_8518]
                · norm_num [dusartPrimeRow_of_explicit_8518]
                · apply DusartPrimeRowsChain.empty
                  norm_num [dusartPrimeRow_of_explicit_8518, dusartPrimeRow_of_explicit_right]

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_8111_8520_part03 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_8518 (p := 8263) (q := 8269) (by exact lowPrime_8269) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8518 (p := 8269) (q := 8273) (by exact lowPrime_8273) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8518 (p := 8273) (q := 8287) (by exact lowPrime_8287) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8518 (p := 8287) (q := 8291) (by exact lowPrime_8291) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8518 (p := 8291) (q := 8293) (by exact lowPrime_8293) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8518 (p := 8293) (q := 8297) (by exact lowPrime_8297) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8518 (p := 8297) (q := 8311) (by exact lowPrime_8311) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8518 (p := 8311) (q := 8317) (by exact lowPrime_8317) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_8111_8520_part03_chain :
    DusartPrimeRowsChain 8263 8316 dusartPrimeRows_8111_8520_part03 := by
  apply DusartPrimeRowsChain.cons
  · norm_num [dusartPrimeRow_of_explicit_8518]
  · norm_num [dusartPrimeRow_of_explicit_8518]
  · apply DusartPrimeRowsChain.cons
    · norm_num [dusartPrimeRow_of_explicit_8518]
    · norm_num [dusartPrimeRow_of_explicit_8518]
    · apply DusartPrimeRowsChain.cons
      · norm_num [dusartPrimeRow_of_explicit_8518]
      · norm_num [dusartPrimeRow_of_explicit_8518]
      · apply DusartPrimeRowsChain.cons
        · norm_num [dusartPrimeRow_of_explicit_8518]
        · norm_num [dusartPrimeRow_of_explicit_8518]
        · apply DusartPrimeRowsChain.cons
          · norm_num [dusartPrimeRow_of_explicit_8518]
          · norm_num [dusartPrimeRow_of_explicit_8518]
          · apply DusartPrimeRowsChain.cons
            · norm_num [dusartPrimeRow_of_explicit_8518]
            · norm_num [dusartPrimeRow_of_explicit_8518]
            · apply DusartPrimeRowsChain.cons
              · norm_num [dusartPrimeRow_of_explicit_8518]
              · norm_num [dusartPrimeRow_of_explicit_8518]
              · apply DusartPrimeRowsChain.cons
                · norm_num [dusartPrimeRow_of_explicit_8518]
                · norm_num [dusartPrimeRow_of_explicit_8518]
                · apply DusartPrimeRowsChain.empty
                  norm_num [dusartPrimeRow_of_explicit_8518, dusartPrimeRow_of_explicit_right]

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_8111_8520_part04 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_8518 (p := 8317) (q := 8329) (by exact lowPrime_8329) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8518 (p := 8329) (q := 8353) (by exact lowPrime_8353) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8518 (p := 8353) (q := 8363) (by exact lowPrime_8363) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8518 (p := 8363) (q := 8369) (by exact lowPrime_8369) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8518 (p := 8369) (q := 8377) (by exact lowPrime_8377) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8518 (p := 8377) (q := 8387) (by exact lowPrime_8387) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8518 (p := 8387) (q := 8389) (by exact lowPrime_8389) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8518 (p := 8389) (q := 8419) (by exact lowPrime_8419) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_8111_8520_part04_chain :
    DusartPrimeRowsChain 8317 8418 dusartPrimeRows_8111_8520_part04 := by
  apply DusartPrimeRowsChain.cons
  · norm_num [dusartPrimeRow_of_explicit_8518]
  · norm_num [dusartPrimeRow_of_explicit_8518]
  · apply DusartPrimeRowsChain.cons
    · norm_num [dusartPrimeRow_of_explicit_8518]
    · norm_num [dusartPrimeRow_of_explicit_8518]
    · apply DusartPrimeRowsChain.cons
      · norm_num [dusartPrimeRow_of_explicit_8518]
      · norm_num [dusartPrimeRow_of_explicit_8518]
      · apply DusartPrimeRowsChain.cons
        · norm_num [dusartPrimeRow_of_explicit_8518]
        · norm_num [dusartPrimeRow_of_explicit_8518]
        · apply DusartPrimeRowsChain.cons
          · norm_num [dusartPrimeRow_of_explicit_8518]
          · norm_num [dusartPrimeRow_of_explicit_8518]
          · apply DusartPrimeRowsChain.cons
            · norm_num [dusartPrimeRow_of_explicit_8518]
            · norm_num [dusartPrimeRow_of_explicit_8518]
            · apply DusartPrimeRowsChain.cons
              · norm_num [dusartPrimeRow_of_explicit_8518]
              · norm_num [dusartPrimeRow_of_explicit_8518]
              · apply DusartPrimeRowsChain.cons
                · norm_num [dusartPrimeRow_of_explicit_8518]
                · norm_num [dusartPrimeRow_of_explicit_8518]
                · apply DusartPrimeRowsChain.empty
                  norm_num [dusartPrimeRow_of_explicit_8518, dusartPrimeRow_of_explicit_right]

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_8111_8520_part05 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_8518 (p := 8419) (q := 8423) (by exact lowPrime_8423) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8518 (p := 8423) (q := 8429) (by exact lowPrime_8429) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8518 (p := 8429) (q := 8431) (by exact lowPrime_8431) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8518 (p := 8431) (q := 8443) (by exact lowPrime_8443) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8518 (p := 8443) (q := 8447) (by exact lowPrime_8447) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8518 (p := 8447) (q := 8461) (by exact lowPrime_8461) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8518 (p := 8461) (q := 8467) (by exact lowPrime_8467) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8518 (p := 8467) (q := 8501) (by exact lowPrime_8501) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_8111_8520_part05_chain :
    DusartPrimeRowsChain 8419 8500 dusartPrimeRows_8111_8520_part05 := by
  apply DusartPrimeRowsChain.cons
  · norm_num [dusartPrimeRow_of_explicit_8518]
  · norm_num [dusartPrimeRow_of_explicit_8518]
  · apply DusartPrimeRowsChain.cons
    · norm_num [dusartPrimeRow_of_explicit_8518]
    · norm_num [dusartPrimeRow_of_explicit_8518]
    · apply DusartPrimeRowsChain.cons
      · norm_num [dusartPrimeRow_of_explicit_8518]
      · norm_num [dusartPrimeRow_of_explicit_8518]
      · apply DusartPrimeRowsChain.cons
        · norm_num [dusartPrimeRow_of_explicit_8518]
        · norm_num [dusartPrimeRow_of_explicit_8518]
        · apply DusartPrimeRowsChain.cons
          · norm_num [dusartPrimeRow_of_explicit_8518]
          · norm_num [dusartPrimeRow_of_explicit_8518]
          · apply DusartPrimeRowsChain.cons
            · norm_num [dusartPrimeRow_of_explicit_8518]
            · norm_num [dusartPrimeRow_of_explicit_8518]
            · apply DusartPrimeRowsChain.cons
              · norm_num [dusartPrimeRow_of_explicit_8518]
              · norm_num [dusartPrimeRow_of_explicit_8518]
              · apply DusartPrimeRowsChain.cons
                · norm_num [dusartPrimeRow_of_explicit_8518]
                · norm_num [dusartPrimeRow_of_explicit_8518]
                · apply DusartPrimeRowsChain.empty
                  norm_num [dusartPrimeRow_of_explicit_8518, dusartPrimeRow_of_explicit_right]

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_8111_8520_part06 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_8518 (p := 8501) (q := 8513) (by exact lowPrime_8513) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8518 (p := 8513) (q := 8521) (by exact lowPrime_8521) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_8111_8520_part06_chain :
    DusartPrimeRowsChain 8501 8520 dusartPrimeRows_8111_8520_part06 := by
  apply DusartPrimeRowsChain.cons
  · norm_num [dusartPrimeRow_of_explicit_8518]
  · norm_num [dusartPrimeRow_of_explicit_8518]
  · apply DusartPrimeRowsChain.cons
    · norm_num [dusartPrimeRow_of_explicit_8518]
    · norm_num [dusartPrimeRow_of_explicit_8518]
    · apply DusartPrimeRowsChain.empty
      norm_num [dusartPrimeRow_of_explicit_8518, dusartPrimeRow_of_explicit_right]

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_8521_8962_part01 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_8955 (p := 8521) (q := 8527) (by exact lowPrime_8527) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8955 (p := 8527) (q := 8537) (by exact lowPrime_8537) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8955 (p := 8537) (q := 8539) (by exact lowPrime_8539) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8955 (p := 8539) (q := 8543) (by exact lowPrime_8543) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8955 (p := 8543) (q := 8563) (by exact lowPrime_8563) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8955 (p := 8563) (q := 8573) (by exact lowPrime_8573) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8955 (p := 8573) (q := 8581) (by exact lowPrime_8581) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8955 (p := 8581) (q := 8597) (by exact lowPrime_8597) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_8521_8962_part01_chain :
    DusartPrimeRowsChain 8521 8596 dusartPrimeRows_8521_8962_part01 := by
  apply DusartPrimeRowsChain.cons
  · norm_num [dusartPrimeRow_of_explicit_8955]
  · norm_num [dusartPrimeRow_of_explicit_8955]
  · apply DusartPrimeRowsChain.cons
    · norm_num [dusartPrimeRow_of_explicit_8955]
    · norm_num [dusartPrimeRow_of_explicit_8955]
    · apply DusartPrimeRowsChain.cons
      · norm_num [dusartPrimeRow_of_explicit_8955]
      · norm_num [dusartPrimeRow_of_explicit_8955]
      · apply DusartPrimeRowsChain.cons
        · norm_num [dusartPrimeRow_of_explicit_8955]
        · norm_num [dusartPrimeRow_of_explicit_8955]
        · apply DusartPrimeRowsChain.cons
          · norm_num [dusartPrimeRow_of_explicit_8955]
          · norm_num [dusartPrimeRow_of_explicit_8955]
          · apply DusartPrimeRowsChain.cons
            · norm_num [dusartPrimeRow_of_explicit_8955]
            · norm_num [dusartPrimeRow_of_explicit_8955]
            · apply DusartPrimeRowsChain.cons
              · norm_num [dusartPrimeRow_of_explicit_8955]
              · norm_num [dusartPrimeRow_of_explicit_8955]
              · apply DusartPrimeRowsChain.cons
                · norm_num [dusartPrimeRow_of_explicit_8955]
                · norm_num [dusartPrimeRow_of_explicit_8955]
                · apply DusartPrimeRowsChain.empty
                  norm_num [dusartPrimeRow_of_explicit_8955, dusartPrimeRow_of_explicit_right]

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_8521_8962_part02 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_8955 (p := 8597) (q := 8599) (by exact lowPrime_8599) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8955 (p := 8599) (q := 8609) (by exact lowPrime_8609) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8955 (p := 8609) (q := 8623) (by exact lowPrime_8623) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8955 (p := 8623) (q := 8627) (by exact lowPrime_8627) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8955 (p := 8627) (q := 8629) (by exact lowPrime_8629) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8955 (p := 8629) (q := 8641) (by exact lowPrime_8641) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8955 (p := 8641) (q := 8647) (by exact lowPrime_8647) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8955 (p := 8647) (q := 8663) (by exact lowPrime_8663) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_8521_8962_part02_chain :
    DusartPrimeRowsChain 8597 8662 dusartPrimeRows_8521_8962_part02 := by
  apply DusartPrimeRowsChain.cons
  · norm_num [dusartPrimeRow_of_explicit_8955]
  · norm_num [dusartPrimeRow_of_explicit_8955]
  · apply DusartPrimeRowsChain.cons
    · norm_num [dusartPrimeRow_of_explicit_8955]
    · norm_num [dusartPrimeRow_of_explicit_8955]
    · apply DusartPrimeRowsChain.cons
      · norm_num [dusartPrimeRow_of_explicit_8955]
      · norm_num [dusartPrimeRow_of_explicit_8955]
      · apply DusartPrimeRowsChain.cons
        · norm_num [dusartPrimeRow_of_explicit_8955]
        · norm_num [dusartPrimeRow_of_explicit_8955]
        · apply DusartPrimeRowsChain.cons
          · norm_num [dusartPrimeRow_of_explicit_8955]
          · norm_num [dusartPrimeRow_of_explicit_8955]
          · apply DusartPrimeRowsChain.cons
            · norm_num [dusartPrimeRow_of_explicit_8955]
            · norm_num [dusartPrimeRow_of_explicit_8955]
            · apply DusartPrimeRowsChain.cons
              · norm_num [dusartPrimeRow_of_explicit_8955]
              · norm_num [dusartPrimeRow_of_explicit_8955]
              · apply DusartPrimeRowsChain.cons
                · norm_num [dusartPrimeRow_of_explicit_8955]
                · norm_num [dusartPrimeRow_of_explicit_8955]
                · apply DusartPrimeRowsChain.empty
                  norm_num [dusartPrimeRow_of_explicit_8955, dusartPrimeRow_of_explicit_right]

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_8521_8962_part03 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_8955 (p := 8663) (q := 8669) (by exact lowPrime_8669) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8955 (p := 8669) (q := 8677) (by exact lowPrime_8677) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8955 (p := 8677) (q := 8681) (by exact lowPrime_8681) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8955 (p := 8681) (q := 8689) (by exact lowPrime_8689) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8955 (p := 8689) (q := 8693) (by exact lowPrime_8693) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8955 (p := 8693) (q := 8699) (by exact lowPrime_8699) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8955 (p := 8699) (q := 8707) (by exact lowPrime_8707) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8955 (p := 8707) (q := 8713) (by exact lowPrime_8713) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_8521_8962_part03_chain :
    DusartPrimeRowsChain 8663 8712 dusartPrimeRows_8521_8962_part03 := by
  apply DusartPrimeRowsChain.cons
  · norm_num [dusartPrimeRow_of_explicit_8955]
  · norm_num [dusartPrimeRow_of_explicit_8955]
  · apply DusartPrimeRowsChain.cons
    · norm_num [dusartPrimeRow_of_explicit_8955]
    · norm_num [dusartPrimeRow_of_explicit_8955]
    · apply DusartPrimeRowsChain.cons
      · norm_num [dusartPrimeRow_of_explicit_8955]
      · norm_num [dusartPrimeRow_of_explicit_8955]
      · apply DusartPrimeRowsChain.cons
        · norm_num [dusartPrimeRow_of_explicit_8955]
        · norm_num [dusartPrimeRow_of_explicit_8955]
        · apply DusartPrimeRowsChain.cons
          · norm_num [dusartPrimeRow_of_explicit_8955]
          · norm_num [dusartPrimeRow_of_explicit_8955]
          · apply DusartPrimeRowsChain.cons
            · norm_num [dusartPrimeRow_of_explicit_8955]
            · norm_num [dusartPrimeRow_of_explicit_8955]
            · apply DusartPrimeRowsChain.cons
              · norm_num [dusartPrimeRow_of_explicit_8955]
              · norm_num [dusartPrimeRow_of_explicit_8955]
              · apply DusartPrimeRowsChain.cons
                · norm_num [dusartPrimeRow_of_explicit_8955]
                · norm_num [dusartPrimeRow_of_explicit_8955]
                · apply DusartPrimeRowsChain.empty
                  norm_num [dusartPrimeRow_of_explicit_8955, dusartPrimeRow_of_explicit_right]

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_8521_8962_part04 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_8955 (p := 8713) (q := 8719) (by exact lowPrime_8719) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8955 (p := 8719) (q := 8731) (by exact lowPrime_8731) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8955 (p := 8731) (q := 8737) (by exact lowPrime_8737) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8955 (p := 8737) (q := 8741) (by exact lowPrime_8741) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8955 (p := 8741) (q := 8747) (by exact lowPrime_8747) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8955 (p := 8747) (q := 8753) (by exact lowPrime_8753) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8955 (p := 8753) (q := 8761) (by exact lowPrime_8761) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8955 (p := 8761) (q := 8779) (by exact lowPrime_8779) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_8521_8962_part04_chain :
    DusartPrimeRowsChain 8713 8778 dusartPrimeRows_8521_8962_part04 := by
  apply DusartPrimeRowsChain.cons
  · norm_num [dusartPrimeRow_of_explicit_8955]
  · norm_num [dusartPrimeRow_of_explicit_8955]
  · apply DusartPrimeRowsChain.cons
    · norm_num [dusartPrimeRow_of_explicit_8955]
    · norm_num [dusartPrimeRow_of_explicit_8955]
    · apply DusartPrimeRowsChain.cons
      · norm_num [dusartPrimeRow_of_explicit_8955]
      · norm_num [dusartPrimeRow_of_explicit_8955]
      · apply DusartPrimeRowsChain.cons
        · norm_num [dusartPrimeRow_of_explicit_8955]
        · norm_num [dusartPrimeRow_of_explicit_8955]
        · apply DusartPrimeRowsChain.cons
          · norm_num [dusartPrimeRow_of_explicit_8955]
          · norm_num [dusartPrimeRow_of_explicit_8955]
          · apply DusartPrimeRowsChain.cons
            · norm_num [dusartPrimeRow_of_explicit_8955]
            · norm_num [dusartPrimeRow_of_explicit_8955]
            · apply DusartPrimeRowsChain.cons
              · norm_num [dusartPrimeRow_of_explicit_8955]
              · norm_num [dusartPrimeRow_of_explicit_8955]
              · apply DusartPrimeRowsChain.cons
                · norm_num [dusartPrimeRow_of_explicit_8955]
                · norm_num [dusartPrimeRow_of_explicit_8955]
                · apply DusartPrimeRowsChain.empty
                  norm_num [dusartPrimeRow_of_explicit_8955, dusartPrimeRow_of_explicit_right]

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_8521_8962_part05 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_8955 (p := 8779) (q := 8783) (by exact lowPrime_8783) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8955 (p := 8783) (q := 8803) (by exact lowPrime_8803) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8955 (p := 8803) (q := 8807) (by exact lowPrime_8807) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8955 (p := 8807) (q := 8819) (by exact lowPrime_8819) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8955 (p := 8819) (q := 8821) (by exact lowPrime_8821) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8955 (p := 8821) (q := 8831) (by exact lowPrime_8831) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8955 (p := 8831) (q := 8837) (by exact lowPrime_8837) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8955 (p := 8837) (q := 8839) (by exact lowPrime_8839) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_8521_8962_part05_chain :
    DusartPrimeRowsChain 8779 8838 dusartPrimeRows_8521_8962_part05 := by
  apply DusartPrimeRowsChain.cons
  · norm_num [dusartPrimeRow_of_explicit_8955]
  · norm_num [dusartPrimeRow_of_explicit_8955]
  · apply DusartPrimeRowsChain.cons
    · norm_num [dusartPrimeRow_of_explicit_8955]
    · norm_num [dusartPrimeRow_of_explicit_8955]
    · apply DusartPrimeRowsChain.cons
      · norm_num [dusartPrimeRow_of_explicit_8955]
      · norm_num [dusartPrimeRow_of_explicit_8955]
      · apply DusartPrimeRowsChain.cons
        · norm_num [dusartPrimeRow_of_explicit_8955]
        · norm_num [dusartPrimeRow_of_explicit_8955]
        · apply DusartPrimeRowsChain.cons
          · norm_num [dusartPrimeRow_of_explicit_8955]
          · norm_num [dusartPrimeRow_of_explicit_8955]
          · apply DusartPrimeRowsChain.cons
            · norm_num [dusartPrimeRow_of_explicit_8955]
            · norm_num [dusartPrimeRow_of_explicit_8955]
            · apply DusartPrimeRowsChain.cons
              · norm_num [dusartPrimeRow_of_explicit_8955]
              · norm_num [dusartPrimeRow_of_explicit_8955]
              · apply DusartPrimeRowsChain.cons
                · norm_num [dusartPrimeRow_of_explicit_8955]
                · norm_num [dusartPrimeRow_of_explicit_8955]
                · apply DusartPrimeRowsChain.empty
                  norm_num [dusartPrimeRow_of_explicit_8955, dusartPrimeRow_of_explicit_right]

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_8521_8962_part06 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_8955 (p := 8839) (q := 8849) (by exact lowPrime_8849) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8955 (p := 8849) (q := 8861) (by exact lowPrime_8861) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8955 (p := 8861) (q := 8863) (by exact lowPrime_8863) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8955 (p := 8863) (q := 8867) (by exact lowPrime_8867) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8955 (p := 8867) (q := 8887) (by exact lowPrime_8887) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8955 (p := 8887) (q := 8893) (by exact lowPrime_8893) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8955 (p := 8893) (q := 8923) (by exact lowPrime_8923) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8955 (p := 8923) (q := 8929) (by exact lowPrime_8929) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_8521_8962_part06_chain :
    DusartPrimeRowsChain 8839 8928 dusartPrimeRows_8521_8962_part06 := by
  apply DusartPrimeRowsChain.cons
  · norm_num [dusartPrimeRow_of_explicit_8955]
  · norm_num [dusartPrimeRow_of_explicit_8955]
  · apply DusartPrimeRowsChain.cons
    · norm_num [dusartPrimeRow_of_explicit_8955]
    · norm_num [dusartPrimeRow_of_explicit_8955]
    · apply DusartPrimeRowsChain.cons
      · norm_num [dusartPrimeRow_of_explicit_8955]
      · norm_num [dusartPrimeRow_of_explicit_8955]
      · apply DusartPrimeRowsChain.cons
        · norm_num [dusartPrimeRow_of_explicit_8955]
        · norm_num [dusartPrimeRow_of_explicit_8955]
        · apply DusartPrimeRowsChain.cons
          · norm_num [dusartPrimeRow_of_explicit_8955]
          · norm_num [dusartPrimeRow_of_explicit_8955]
          · apply DusartPrimeRowsChain.cons
            · norm_num [dusartPrimeRow_of_explicit_8955]
            · norm_num [dusartPrimeRow_of_explicit_8955]
            · apply DusartPrimeRowsChain.cons
              · norm_num [dusartPrimeRow_of_explicit_8955]
              · norm_num [dusartPrimeRow_of_explicit_8955]
              · apply DusartPrimeRowsChain.cons
                · norm_num [dusartPrimeRow_of_explicit_8955]
                · norm_num [dusartPrimeRow_of_explicit_8955]
                · apply DusartPrimeRowsChain.empty
                  norm_num [dusartPrimeRow_of_explicit_8955, dusartPrimeRow_of_explicit_right]

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_8521_8962_part07 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_8955 (p := 8929) (q := 8933) (by exact lowPrime_8933) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8955 (p := 8933) (q := 8941) (by exact lowPrime_8941) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8955 (p := 8941) (q := 8951) (by exact lowPrime_8951) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8955 (p := 8951) (q := 8963) (by exact lowPrime_8963) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_8521_8962_part07_chain :
    DusartPrimeRowsChain 8929 8962 dusartPrimeRows_8521_8962_part07 := by
  apply DusartPrimeRowsChain.cons
  · norm_num [dusartPrimeRow_of_explicit_8955]
  · norm_num [dusartPrimeRow_of_explicit_8955]
  · apply DusartPrimeRowsChain.cons
    · norm_num [dusartPrimeRow_of_explicit_8955]
    · norm_num [dusartPrimeRow_of_explicit_8955]
    · apply DusartPrimeRowsChain.cons
      · norm_num [dusartPrimeRow_of_explicit_8955]
      · norm_num [dusartPrimeRow_of_explicit_8955]
      · apply DusartPrimeRowsChain.cons
        · norm_num [dusartPrimeRow_of_explicit_8955]
        · norm_num [dusartPrimeRow_of_explicit_8955]
        · apply DusartPrimeRowsChain.empty
          norm_num [dusartPrimeRow_of_explicit_8955, dusartPrimeRow_of_explicit_right]
