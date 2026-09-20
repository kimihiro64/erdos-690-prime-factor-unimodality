import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowBase

set_option autoImplicit false
set_option maxRecDepth 1000000

/-! # Lower finite Dusart prefix chunk 14 -/

namespace PrimeFactorUnimodality

noncomputable section
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_14153 : Nat.Prime 14153 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 14153 14152 1 3 [2, 2, 2, 29, 61]
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
    · apply IsUnit.of_mul_eq_one (7076 : ZMod 14153)
      decide
    · apply IsUnit.of_mul_eq_one (2649 : ZMod 14153)
      decide
    · apply IsUnit.of_mul_eq_one (4356 : ZMod 14153)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_14159 : Nat.Prime 14159 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 14159 14158 1 13 [2, 7079]
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
    · apply IsUnit.of_mul_eq_one (7079 : ZMod 14159)
      decide
    · apply IsUnit.of_mul_eq_one (2107 : ZMod 14159)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_14173 : Nat.Prime 14173 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 14173 14172 1 2 [2, 2, 3, 1181]
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
    · apply IsUnit.of_mul_eq_one (7086 : ZMod 14173)
      decide
    · apply IsUnit.of_mul_eq_one (8277 : ZMod 14173)
      decide
    · apply IsUnit.of_mul_eq_one (5998 : ZMod 14173)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_14177 : Nat.Prime 14177 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 14177 14176 1 3 [2, 2, 2, 2, 2, 443]
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
    · apply IsUnit.of_mul_eq_one (7088 : ZMod 14177)
      decide
    · apply IsUnit.of_mul_eq_one (12653 : ZMod 14177)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_14197 : Nat.Prime 14197 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 14197 14196 1 11 [2, 2, 3, 7, 13, 13]
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
    · apply IsUnit.of_mul_eq_one (7098 : ZMod 14197)
      decide
    · apply IsUnit.of_mul_eq_one (3024 : ZMod 14197)
      decide
    · apply IsUnit.of_mul_eq_one (9977 : ZMod 14197)
      decide
    · apply IsUnit.of_mul_eq_one (2297 : ZMod 14197)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_14207 : Nat.Prime 14207 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 14207 14206 1 5 [2, 7103]
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
    · apply IsUnit.of_mul_eq_one (7103 : ZMod 14207)
      decide
    · apply IsUnit.of_mul_eq_one (592 : ZMod 14207)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_14221 : Nat.Prime 14221 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 14221 14220 1 2 [2, 2, 3, 3, 5, 79]
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
    · apply IsUnit.of_mul_eq_one (7110 : ZMod 14221)
      decide
    · apply IsUnit.of_mul_eq_one (6355 : ZMod 14221)
      decide
    · apply IsUnit.of_mul_eq_one (7151 : ZMod 14221)
      decide
    · apply IsUnit.of_mul_eq_one (8558 : ZMod 14221)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_14243 : Nat.Prime 14243 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 14243 14242 1 2 [2, 7121]
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
    · apply IsUnit.of_mul_eq_one (7121 : ZMod 14243)
      decide
    · apply IsUnit.of_mul_eq_one (4748 : ZMod 14243)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_14249 : Nat.Prime 14249 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 14249 14248 1 3 [2, 2, 2, 13, 137]
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
    · apply IsUnit.of_mul_eq_one (7124 : ZMod 14249)
      decide
    · apply IsUnit.of_mul_eq_one (11654 : ZMod 14249)
      decide
    · apply IsUnit.of_mul_eq_one (8319 : ZMod 14249)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_14251 : Nat.Prime 14251 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 14251 14250 1 3 [2, 3, 5, 5, 5, 19]
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
    · apply IsUnit.of_mul_eq_one (7125 : ZMod 14251)
      decide
    · apply IsUnit.of_mul_eq_one (2800 : ZMod 14251)
      decide
    · apply IsUnit.of_mul_eq_one (8142 : ZMod 14251)
      decide
    · apply IsUnit.of_mul_eq_one (4205 : ZMod 14251)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_14281 : Nat.Prime 14281 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 14281 14280 1 19 [2, 2, 2, 3, 5, 7, 17]
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
    · apply IsUnit.of_mul_eq_one (7140 : ZMod 14281)
      decide
    · apply IsUnit.of_mul_eq_one (9560 : ZMod 14281)
      decide
    · apply IsUnit.of_mul_eq_one (7194 : ZMod 14281)
      decide
    · apply IsUnit.of_mul_eq_one (9439 : ZMod 14281)
      decide
    · apply IsUnit.of_mul_eq_one (11150 : ZMod 14281)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_14293 : Nat.Prime 14293 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 14293 14292 1 6 [2, 2, 3, 3, 397]
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
    · apply IsUnit.of_mul_eq_one (7146 : ZMod 14293)
      decide
    · apply IsUnit.of_mul_eq_one (13679 : ZMod 14293)
      decide
    · apply IsUnit.of_mul_eq_one (1679 : ZMod 14293)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_14303 : Nat.Prime 14303 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 14303 14302 1 5 [2, 7151]
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
    · apply IsUnit.of_mul_eq_one (7151 : ZMod 14303)
      decide
    · apply IsUnit.of_mul_eq_one (596 : ZMod 14303)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_14321 : Nat.Prime 14321 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 14321 14320 1 3 [2, 2, 2, 2, 5, 179]
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
    · apply IsUnit.of_mul_eq_one (7160 : ZMod 14321)
      decide
    · apply IsUnit.of_mul_eq_one (13722 : ZMod 14321)
      decide
    · apply IsUnit.of_mul_eq_one (9776 : ZMod 14321)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_14323 : Nat.Prime 14323 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 14323 14322 1 5 [2, 3, 7, 11, 31]
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
    · apply IsUnit.of_mul_eq_one (7161 : ZMod 14323)
      decide
    · apply IsUnit.of_mul_eq_one (12779 : ZMod 14323)
      decide
    · apply IsUnit.of_mul_eq_one (10494 : ZMod 14323)
      decide
    · apply IsUnit.of_mul_eq_one (2467 : ZMod 14323)
      decide
    · apply IsUnit.of_mul_eq_one (2051 : ZMod 14323)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_14327 : Nat.Prime 14327 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 14327 14326 1 5 [2, 13, 19, 29]
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
    · apply IsUnit.of_mul_eq_one (7163 : ZMod 14327)
      decide
    · apply IsUnit.of_mul_eq_one (11573 : ZMod 14327)
      decide
    · apply IsUnit.of_mul_eq_one (7610 : ZMod 14327)
      decide
    · apply IsUnit.of_mul_eq_one (6669 : ZMod 14327)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_14341 : Nat.Prime 14341 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 14341 14340 1 2 [2, 2, 3, 5, 239]
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
    · apply IsUnit.of_mul_eq_one (7170 : ZMod 14341)
      decide
    · apply IsUnit.of_mul_eq_one (7440 : ZMod 14341)
      decide
    · apply IsUnit.of_mul_eq_one (4814 : ZMod 14341)
      decide
    · apply IsUnit.of_mul_eq_one (8442 : ZMod 14341)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_14347 : Nat.Prime 14347 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 14347 14346 1 3 [2, 3, 3, 797]
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
    · apply IsUnit.of_mul_eq_one (7173 : ZMod 14347)
      decide
    · apply IsUnit.of_mul_eq_one (8074 : ZMod 14347)
      decide
    · apply IsUnit.of_mul_eq_one (445 : ZMod 14347)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_14369 : Nat.Prime 14369 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 14369 14368 1 3 [2, 2, 2, 2, 2, 449]
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
    · apply IsUnit.of_mul_eq_one (7184 : ZMod 14369)
      decide
    · apply IsUnit.of_mul_eq_one (11784 : ZMod 14369)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_14387 : Nat.Prime 14387 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 14387 14386 1 2 [2, 7193]
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
    · apply IsUnit.of_mul_eq_one (7193 : ZMod 14387)
      decide
    · apply IsUnit.of_mul_eq_one (4796 : ZMod 14387)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_14389 : Nat.Prime 14389 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 14389 14388 1 2 [2, 2, 3, 11, 109]
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
    · apply IsUnit.of_mul_eq_one (7194 : ZMod 14389)
      decide
    · apply IsUnit.of_mul_eq_one (4940 : ZMod 14389)
      decide
    · apply IsUnit.of_mul_eq_one (10589 : ZMod 14389)
      decide
    · apply IsUnit.of_mul_eq_one (11347 : ZMod 14389)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_14401 : Nat.Prime 14401 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 14401 14400 1 11 [2, 2, 2, 2, 2, 2, 3, 3, 5, 5]
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
    · apply IsUnit.of_mul_eq_one (7200 : ZMod 14401)
      decide
    · apply IsUnit.of_mul_eq_one (4694 : ZMod 14401)
      decide
    · apply IsUnit.of_mul_eq_one (1139 : ZMod 14401)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_14407 : Nat.Prime 14407 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 14407 14406 1 19 [2, 3, 7, 7, 7, 7]
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
    · apply IsUnit.of_mul_eq_one (7203 : ZMod 14407)
      decide
    · apply IsUnit.of_mul_eq_one (5907 : ZMod 14407)
      decide
    · apply IsUnit.of_mul_eq_one (8040 : ZMod 14407)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_14411 : Nat.Prime 14411 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 14411 14410 1 2 [2, 5, 11, 131]
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
    · apply IsUnit.of_mul_eq_one (7205 : ZMod 14411)
      decide
    · apply IsUnit.of_mul_eq_one (10844 : ZMod 14411)
      decide
    · apply IsUnit.of_mul_eq_one (5190 : ZMod 14411)
      decide
    · apply IsUnit.of_mul_eq_one (7605 : ZMod 14411)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_14419 : Nat.Prime 14419 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 14419 14418 1 2 [2, 3, 3, 3, 3, 89]
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
    · apply IsUnit.of_mul_eq_one (7209 : ZMod 14419)
      decide
    · apply IsUnit.of_mul_eq_one (7402 : ZMod 14419)
      decide
    · apply IsUnit.of_mul_eq_one (12556 : ZMod 14419)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_14423 : Nat.Prime 14423 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 14423 14422 1 5 [2, 7211]
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
    · apply IsUnit.of_mul_eq_one (7211 : ZMod 14423)
      decide
    · apply IsUnit.of_mul_eq_one (601 : ZMod 14423)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_14431 : Nat.Prime 14431 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 14431 14430 1 3 [2, 3, 5, 13, 37]
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
    · apply IsUnit.of_mul_eq_one (7215 : ZMod 14431)
      decide
    · apply IsUnit.of_mul_eq_one (183 : ZMod 14431)
      decide
    · apply IsUnit.of_mul_eq_one (8290 : ZMod 14431)
      decide
    · apply IsUnit.of_mul_eq_one (8085 : ZMod 14431)
      decide
    · apply IsUnit.of_mul_eq_one (8644 : ZMod 14431)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_14437 : Nat.Prime 14437 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 14437 14436 1 5 [2, 2, 3, 3, 401]
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
    · apply IsUnit.of_mul_eq_one (7218 : ZMod 14437)
      decide
    · apply IsUnit.of_mul_eq_one (11119 : ZMod 14437)
      decide
    · apply IsUnit.of_mul_eq_one (5437 : ZMod 14437)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_14447 : Nat.Prime 14447 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 14447 14446 1 5 [2, 31, 233]
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
    · apply IsUnit.of_mul_eq_one (7223 : ZMod 14447)
      decide
    · apply IsUnit.of_mul_eq_one (715 : ZMod 14447)
      decide
    · apply IsUnit.of_mul_eq_one (14202 : ZMod 14447)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_14449 : Nat.Prime 14449 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 14449 14448 1 22 [2, 2, 2, 2, 3, 7, 43]
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
    · apply IsUnit.of_mul_eq_one (7224 : ZMod 14449)
      decide
    · apply IsUnit.of_mul_eq_one (10277 : ZMod 14449)
      decide
    · apply IsUnit.of_mul_eq_one (5335 : ZMod 14449)
      decide
    · apply IsUnit.of_mul_eq_one (2888 : ZMod 14449)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_14461 : Nat.Prime 14461 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 14461 14460 1 2 [2, 2, 3, 5, 241]
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
    · apply IsUnit.of_mul_eq_one (7230 : ZMod 14461)
      decide
    · apply IsUnit.of_mul_eq_one (6987 : ZMod 14461)
      decide
    · apply IsUnit.of_mul_eq_one (1223 : ZMod 14461)
      decide
    · apply IsUnit.of_mul_eq_one (985 : ZMod 14461)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_14479 : Nat.Prime 14479 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 14479 14478 1 3 [2, 3, 19, 127]
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
    · apply IsUnit.of_mul_eq_one (7239 : ZMod 14479)
      decide
    · apply IsUnit.of_mul_eq_one (9827 : ZMod 14479)
      decide
    · apply IsUnit.of_mul_eq_one (4435 : ZMod 14479)
      decide
    · apply IsUnit.of_mul_eq_one (8358 : ZMod 14479)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_14489 : Nat.Prime 14489 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 14489 14488 1 3 [2, 2, 2, 1811]
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
    · apply IsUnit.of_mul_eq_one (7244 : ZMod 14489)
      decide
    · apply IsUnit.of_mul_eq_one (11642 : ZMod 14489)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_14503 : Nat.Prime 14503 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 14503 14502 1 3 [2, 3, 2417]
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
    · apply IsUnit.of_mul_eq_one (7251 : ZMod 14503)
      decide
    · apply IsUnit.of_mul_eq_one (8277 : ZMod 14503)
      decide
    · apply IsUnit.of_mul_eq_one (5598 : ZMod 14503)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_14519 : Nat.Prime 14519 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 14519 14518 1 13 [2, 7, 17, 61]
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
    · apply IsUnit.of_mul_eq_one (7259 : ZMod 14519)
      decide
    · apply IsUnit.of_mul_eq_one (4315 : ZMod 14519)
      decide
    · apply IsUnit.of_mul_eq_one (7766 : ZMod 14519)
      decide
    · apply IsUnit.of_mul_eq_one (5722 : ZMod 14519)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_14533 : Nat.Prime 14533 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 14533 14532 1 2 [2, 2, 3, 7, 173]
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
    · apply IsUnit.of_mul_eq_one (7266 : ZMod 14533)
      decide
    · apply IsUnit.of_mul_eq_one (12302 : ZMod 14533)
      decide
    · apply IsUnit.of_mul_eq_one (9414 : ZMod 14533)
      decide
    · apply IsUnit.of_mul_eq_one (10065 : ZMod 14533)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_14537 : Nat.Prime 14537 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 14537 14536 1 3 [2, 2, 2, 23, 79]
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
    · apply IsUnit.of_mul_eq_one (7268 : ZMod 14537)
      decide
    · apply IsUnit.of_mul_eq_one (4092 : ZMod 14537)
      decide
    · apply IsUnit.of_mul_eq_one (2603 : ZMod 14537)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_14543 : Nat.Prime 14543 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 14543 14542 1 5 [2, 11, 661]
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
    · apply IsUnit.of_mul_eq_one (7271 : ZMod 14543)
      decide
    · apply IsUnit.of_mul_eq_one (527 : ZMod 14543)
      decide
    · apply IsUnit.of_mul_eq_one (9003 : ZMod 14543)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_14549 : Nat.Prime 14549 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 14549 14548 1 2 [2, 2, 3637]
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
    · apply IsUnit.of_mul_eq_one (7274 : ZMod 14549)
      decide
    · apply IsUnit.of_mul_eq_one (970 : ZMod 14549)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_14551 : Nat.Prime 14551 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 14551 14550 1 3 [2, 3, 5, 5, 97]
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
    · apply IsUnit.of_mul_eq_one (7275 : ZMod 14551)
      decide
    · apply IsUnit.of_mul_eq_one (13272 : ZMod 14551)
      decide
    · apply IsUnit.of_mul_eq_one (12157 : ZMod 14551)
      decide
    · apply IsUnit.of_mul_eq_one (4288 : ZMod 14551)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_14557 : Nat.Prime 14557 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 14557 14556 1 2 [2, 2, 3, 1213]
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
    · apply IsUnit.of_mul_eq_one (7278 : ZMod 14557)
      decide
    · apply IsUnit.of_mul_eq_one (11778 : ZMod 14557)
      decide
    · apply IsUnit.of_mul_eq_one (10245 : ZMod 14557)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_14561 : Nat.Prime 14561 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 14561 14560 1 6 [2, 2, 2, 2, 2, 5, 7, 13]
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
    · apply IsUnit.of_mul_eq_one (7280 : ZMod 14561)
      decide
    · apply IsUnit.of_mul_eq_one (4203 : ZMod 14561)
      decide
    · apply IsUnit.of_mul_eq_one (2796 : ZMod 14561)
      decide
    · apply IsUnit.of_mul_eq_one (1947 : ZMod 14561)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_14563 : Nat.Prime 14563 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 14563 14562 1 3 [2, 3, 3, 809]
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
    · apply IsUnit.of_mul_eq_one (7281 : ZMod 14563)
      decide
    · apply IsUnit.of_mul_eq_one (3422 : ZMod 14563)
      decide
    · apply IsUnit.of_mul_eq_one (1691 : ZMod 14563)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_14591 : Nat.Prime 14591 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 14591 14590 1 11 [2, 5, 1459]
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
    · apply IsUnit.of_mul_eq_one (7295 : ZMod 14591)
      decide
    · apply IsUnit.of_mul_eq_one (4619 : ZMod 14591)
      decide
    · apply IsUnit.of_mul_eq_one (1339 : ZMod 14591)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_14593 : Nat.Prime 14593 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 14593 14592 1 5 [2, 2, 2, 2, 2, 2, 2, 2, 3, 19]
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
    · apply IsUnit.of_mul_eq_one (7296 : ZMod 14593)
      decide
    · apply IsUnit.of_mul_eq_one (2636 : ZMod 14593)
      decide
    · apply IsUnit.of_mul_eq_one (1013 : ZMod 14593)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_14621 : Nat.Prime 14621 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 14621 14620 1 2 [2, 2, 5, 17, 43]
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
    · apply IsUnit.of_mul_eq_one (7310 : ZMod 14621)
      decide
    · apply IsUnit.of_mul_eq_one (4131 : ZMod 14621)
      decide
    · apply IsUnit.of_mul_eq_one (5640 : ZMod 14621)
      decide
    · apply IsUnit.of_mul_eq_one (13020 : ZMod 14621)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_14627 : Nat.Prime 14627 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 14627 14626 1 2 [2, 71, 103]
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
    · apply IsUnit.of_mul_eq_one (7313 : ZMod 14627)
      decide
    · apply IsUnit.of_mul_eq_one (1662 : ZMod 14627)
      decide
    · apply IsUnit.of_mul_eq_one (9269 : ZMod 14627)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_14629 : Nat.Prime 14629 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 14629 14628 1 2 [2, 2, 3, 23, 53]
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
    · apply IsUnit.of_mul_eq_one (7314 : ZMod 14629)
      decide
    · apply IsUnit.of_mul_eq_one (2491 : ZMod 14629)
      decide
    · apply IsUnit.of_mul_eq_one (2557 : ZMod 14629)
      decide
    · apply IsUnit.of_mul_eq_one (219 : ZMod 14629)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_14633 : Nat.Prime 14633 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 14633 14632 1 3 [2, 2, 2, 31, 59]
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
    · apply IsUnit.of_mul_eq_one (7316 : ZMod 14633)
      decide
    · apply IsUnit.of_mul_eq_one (5497 : ZMod 14633)
      decide
    · apply IsUnit.of_mul_eq_one (4455 : ZMod 14633)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_14639 : Nat.Prime 14639 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 14639 14638 1 11 [2, 13, 563]
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
    · apply IsUnit.of_mul_eq_one (7319 : ZMod 14639)
      decide
    · apply IsUnit.of_mul_eq_one (2738 : ZMod 14639)
      decide
    · apply IsUnit.of_mul_eq_one (12565 : ZMod 14639)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_14653 : Nat.Prime 14653 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 14653 14652 1 2 [2, 2, 3, 3, 11, 37]
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
    · apply IsUnit.of_mul_eq_one (7326 : ZMod 14653)
      decide
    · apply IsUnit.of_mul_eq_one (8537 : ZMod 14653)
      decide
    · apply IsUnit.of_mul_eq_one (6705 : ZMod 14653)
      decide
    · apply IsUnit.of_mul_eq_one (8480 : ZMod 14653)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_14657 : Nat.Prime 14657 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 14657 14656 1 3 [2, 2, 2, 2, 2, 2, 229]
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
    · apply IsUnit.of_mul_eq_one (7328 : ZMod 14657)
      decide
    · apply IsUnit.of_mul_eq_one (10484 : ZMod 14657)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_14669 : Nat.Prime 14669 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 14669 14668 1 2 [2, 2, 19, 193]
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
    · apply IsUnit.of_mul_eq_one (7334 : ZMod 14669)
      decide
    · apply IsUnit.of_mul_eq_one (8211 : ZMod 14669)
      decide
    · apply IsUnit.of_mul_eq_one (5074 : ZMod 14669)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_14683 : Nat.Prime 14683 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 14683 14682 1 3 [2, 3, 2447]
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
    · apply IsUnit.of_mul_eq_one (7341 : ZMod 14683)
      decide
    · apply IsUnit.of_mul_eq_one (13583 : ZMod 14683)
      decide
    · apply IsUnit.of_mul_eq_one (10266 : ZMod 14683)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_14699 : Nat.Prime 14699 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 14699 14698 1 2 [2, 7349]
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
    · apply IsUnit.of_mul_eq_one (7349 : ZMod 14699)
      decide
    · apply IsUnit.of_mul_eq_one (4900 : ZMod 14699)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_14713 : Nat.Prime 14713 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 14713 14712 1 5 [2, 2, 2, 3, 613]
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
    · apply IsUnit.of_mul_eq_one (7356 : ZMod 14713)
      decide
    · apply IsUnit.of_mul_eq_one (252 : ZMod 14713)
      decide
    · apply IsUnit.of_mul_eq_one (4586 : ZMod 14713)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_14717 : Nat.Prime 14717 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 14717 14716 1 2 [2, 2, 13, 283]
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
    · apply IsUnit.of_mul_eq_one (7358 : ZMod 14717)
      decide
    · apply IsUnit.of_mul_eq_one (12473 : ZMod 14717)
      decide
    · apply IsUnit.of_mul_eq_one (7774 : ZMod 14717)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_14723 : Nat.Prime 14723 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 14723 14722 1 2 [2, 17, 433]
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
    · apply IsUnit.of_mul_eq_one (7361 : ZMod 14723)
      decide
    · apply IsUnit.of_mul_eq_one (8205 : ZMod 14723)
      decide
    · apply IsUnit.of_mul_eq_one (5156 : ZMod 14723)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_14731 : Nat.Prime 14731 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 14731 14730 1 10 [2, 3, 5, 491]
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
    · apply IsUnit.of_mul_eq_one (7365 : ZMod 14731)
      decide
    · apply IsUnit.of_mul_eq_one (4274 : ZMod 14731)
      decide
    · apply IsUnit.of_mul_eq_one (14105 : ZMod 14731)
      decide
    · apply IsUnit.of_mul_eq_one (2987 : ZMod 14731)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_14737 : Nat.Prime 14737 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 14737 14736 1 10 [2, 2, 2, 2, 3, 307]
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
    · apply IsUnit.of_mul_eq_one (7368 : ZMod 14737)
      decide
    · apply IsUnit.of_mul_eq_one (6359 : ZMod 14737)
      decide
    · apply IsUnit.of_mul_eq_one (8565 : ZMod 14737)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_14741 : Nat.Prime 14741 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 14741 14740 1 2 [2, 2, 5, 11, 67]
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
    · apply IsUnit.of_mul_eq_one (7370 : ZMod 14741)
      decide
    · apply IsUnit.of_mul_eq_one (14703 : ZMod 14741)
      decide
    · apply IsUnit.of_mul_eq_one (5286 : ZMod 14741)
      decide
    · apply IsUnit.of_mul_eq_one (12019 : ZMod 14741)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_14747 : Nat.Prime 14747 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 14747 14746 1 2 [2, 73, 101]
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
    · apply IsUnit.of_mul_eq_one (7373 : ZMod 14747)
      decide
    · apply IsUnit.of_mul_eq_one (6507 : ZMod 14747)
      decide
    · apply IsUnit.of_mul_eq_one (3481 : ZMod 14747)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_14753 : Nat.Prime 14753 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 14753 14752 1 3 [2, 2, 2, 2, 2, 461]
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
    · apply IsUnit.of_mul_eq_one (7376 : ZMod 14753)
      decide
    · apply IsUnit.of_mul_eq_one (7110 : ZMod 14753)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_14759 : Nat.Prime 14759 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 14759 14758 1 17 [2, 47, 157]
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
    · apply IsUnit.of_mul_eq_one (7379 : ZMod 14759)
      decide
    · apply IsUnit.of_mul_eq_one (2089 : ZMod 14759)
      decide
    · apply IsUnit.of_mul_eq_one (9439 : ZMod 14759)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_14767 : Nat.Prime 14767 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 14767 14766 1 3 [2, 3, 23, 107]
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
    · apply IsUnit.of_mul_eq_one (7383 : ZMod 14767)
      decide
    · apply IsUnit.of_mul_eq_one (1676 : ZMod 14767)
      decide
    · apply IsUnit.of_mul_eq_one (13686 : ZMod 14767)
      decide
    · apply IsUnit.of_mul_eq_one (6270 : ZMod 14767)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_14771 : Nat.Prime 14771 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 14771 14770 1 2 [2, 5, 7, 211]
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
    · apply IsUnit.of_mul_eq_one (7385 : ZMod 14771)
      decide
    · apply IsUnit.of_mul_eq_one (4762 : ZMod 14771)
      decide
    · apply IsUnit.of_mul_eq_one (12421 : ZMod 14771)
      decide
    · apply IsUnit.of_mul_eq_one (613 : ZMod 14771)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_14779 : Nat.Prime 14779 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 14779 14778 1 3 [2, 3, 3, 821]
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
    · apply IsUnit.of_mul_eq_one (7389 : ZMod 14779)
      decide
    · apply IsUnit.of_mul_eq_one (2229 : ZMod 14779)
      decide
    · apply IsUnit.of_mul_eq_one (2075 : ZMod 14779)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_14783 : Nat.Prime 14783 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 14783 14782 1 5 [2, 19, 389]
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
    · apply IsUnit.of_mul_eq_one (7391 : ZMod 14783)
      decide
    · apply IsUnit.of_mul_eq_one (2389 : ZMod 14783)
      decide
    · apply IsUnit.of_mul_eq_one (10717 : ZMod 14783)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_14797 : Nat.Prime 14797 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 14797 14796 1 2 [2, 2, 3, 3, 3, 137]
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
    · apply IsUnit.of_mul_eq_one (7398 : ZMod 14797)
      decide
    · apply IsUnit.of_mul_eq_one (4648 : ZMod 14797)
      decide
    · apply IsUnit.of_mul_eq_one (4826 : ZMod 14797)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_14813 : Nat.Prime 14813 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 14813 14812 1 2 [2, 2, 7, 23, 23]
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
    · apply IsUnit.of_mul_eq_one (7406 : ZMod 14813)
      decide
    · apply IsUnit.of_mul_eq_one (10548 : ZMod 14813)
      decide
    · apply IsUnit.of_mul_eq_one (13469 : ZMod 14813)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_14821 : Nat.Prime 14821 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 14821 14820 1 2 [2, 2, 3, 5, 13, 19]
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
    · apply IsUnit.of_mul_eq_one (7410 : ZMod 14821)
      decide
    · apply IsUnit.of_mul_eq_one (14150 : ZMod 14821)
      decide
    · apply IsUnit.of_mul_eq_one (4607 : ZMod 14821)
      decide
    · apply IsUnit.of_mul_eq_one (6641 : ZMod 14821)
      decide
    · apply IsUnit.of_mul_eq_one (9334 : ZMod 14821)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_14827 : Nat.Prime 14827 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 14827 14826 1 2 [2, 3, 7, 353]
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
    · apply IsUnit.of_mul_eq_one (7413 : ZMod 14827)
      decide
    · apply IsUnit.of_mul_eq_one (7320 : ZMod 14827)
      decide
    · apply IsUnit.of_mul_eq_one (6715 : ZMod 14827)
      decide
    · apply IsUnit.of_mul_eq_one (9274 : ZMod 14827)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_14831 : Nat.Prime 14831 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 14831 14830 1 11 [2, 5, 1483]
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
    · apply IsUnit.of_mul_eq_one (7415 : ZMod 14831)
      decide
    · apply IsUnit.of_mul_eq_one (11829 : ZMod 14831)
      decide
    · apply IsUnit.of_mul_eq_one (13667 : ZMod 14831)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_14843 : Nat.Prime 14843 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 14843 14842 1 2 [2, 41, 181]
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
    · apply IsUnit.of_mul_eq_one (7421 : ZMod 14843)
      decide
    · apply IsUnit.of_mul_eq_one (4039 : ZMod 14843)
      decide
    · apply IsUnit.of_mul_eq_one (1614 : ZMod 14843)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_14851 : Nat.Prime 14851 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 14851 14850 1 2 [2, 3, 3, 3, 5, 5, 11]
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
    · apply IsUnit.of_mul_eq_one (7425 : ZMod 14851)
      decide
    · apply IsUnit.of_mul_eq_one (4005 : ZMod 14851)
      decide
    · apply IsUnit.of_mul_eq_one (9599 : ZMod 14851)
      decide
    · apply IsUnit.of_mul_eq_one (14426 : ZMod 14851)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_14867 : Nat.Prime 14867 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 14867 14866 1 2 [2, 7433]
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
    · apply IsUnit.of_mul_eq_one (7433 : ZMod 14867)
      decide
    · apply IsUnit.of_mul_eq_one (4956 : ZMod 14867)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_14869 : Nat.Prime 14869 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 14869 14868 1 2 [2, 2, 3, 3, 7, 59]
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
    · apply IsUnit.of_mul_eq_one (7434 : ZMod 14869)
      decide
    · apply IsUnit.of_mul_eq_one (4000 : ZMod 14869)
      decide
    · apply IsUnit.of_mul_eq_one (2332 : ZMod 14869)
      decide
    · apply IsUnit.of_mul_eq_one (6943 : ZMod 14869)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_14879 : Nat.Prime 14879 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 14879 14878 1 7 [2, 43, 173]
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
    · apply IsUnit.of_mul_eq_one (7439 : ZMod 14879)
      decide
    · apply IsUnit.of_mul_eq_one (3231 : ZMod 14879)
      decide
    · apply IsUnit.of_mul_eq_one (995 : ZMod 14879)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_14887 : Nat.Prime 14887 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 14887 14886 1 3 [2, 3, 3, 827]
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
    · apply IsUnit.of_mul_eq_one (7443 : ZMod 14887)
      decide
    · apply IsUnit.of_mul_eq_one (12385 : ZMod 14887)
      decide
    · apply IsUnit.of_mul_eq_one (4677 : ZMod 14887)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_14891 : Nat.Prime 14891 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 14891 14890 1 2 [2, 5, 1489]
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
    · apply IsUnit.of_mul_eq_one (7445 : ZMod 14891)
      decide
    · apply IsUnit.of_mul_eq_one (13533 : ZMod 14891)
      decide
    · apply IsUnit.of_mul_eq_one (2460 : ZMod 14891)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_14897 : Nat.Prime 14897 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 14897 14896 1 3 [2, 2, 2, 2, 7, 7, 19]
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
    · apply IsUnit.of_mul_eq_one (7448 : ZMod 14897)
      decide
    · apply IsUnit.of_mul_eq_one (959 : ZMod 14897)
      decide
    · apply IsUnit.of_mul_eq_one (6437 : ZMod 14897)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_14923 : Nat.Prime 14923 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 14923 14922 1 2 [2, 3, 3, 829]
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
    · apply IsUnit.of_mul_eq_one (7461 : ZMod 14923)
      decide
    · apply IsUnit.of_mul_eq_one (6385 : ZMod 14923)
      decide
    · apply IsUnit.of_mul_eq_one (3759 : ZMod 14923)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_14929 : Nat.Prime 14929 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 14929 14928 1 7 [2, 2, 2, 2, 3, 311]
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
    · apply IsUnit.of_mul_eq_one (7464 : ZMod 14929)
      decide
    · apply IsUnit.of_mul_eq_one (3575 : ZMod 14929)
      decide
    · apply IsUnit.of_mul_eq_one (13690 : ZMod 14929)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_14939 : Nat.Prime 14939 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 14939 14938 1 2 [2, 7, 11, 97]
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
    · apply IsUnit.of_mul_eq_one (7469 : ZMod 14939)
      decide
    · apply IsUnit.of_mul_eq_one (1327 : ZMod 14939)
      decide
    · apply IsUnit.of_mul_eq_one (175 : ZMod 14939)
      decide
    · apply IsUnit.of_mul_eq_one (662 : ZMod 14939)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_14947 : Nat.Prime 14947 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 14947 14946 1 2 [2, 3, 47, 53]
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
    · apply IsUnit.of_mul_eq_one (7473 : ZMod 14947)
      decide
    · apply IsUnit.of_mul_eq_one (254 : ZMod 14947)
      decide
    · apply IsUnit.of_mul_eq_one (10231 : ZMod 14947)
      decide
    · apply IsUnit.of_mul_eq_one (11356 : ZMod 14947)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_14951 : Nat.Prime 14951 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 14951 14950 1 19 [2, 5, 5, 13, 23]
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
    · apply IsUnit.of_mul_eq_one (7475 : ZMod 14951)
      decide
    · apply IsUnit.of_mul_eq_one (5726 : ZMod 14951)
      decide
    · apply IsUnit.of_mul_eq_one (10447 : ZMod 14951)
      decide
    · apply IsUnit.of_mul_eq_one (11706 : ZMod 14951)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_14957 : Nat.Prime 14957 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 14957 14956 1 2 [2, 2, 3739]
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
    · apply IsUnit.of_mul_eq_one (7478 : ZMod 14957)
      decide
    · apply IsUnit.of_mul_eq_one (6980 : ZMod 14957)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_14969 : Nat.Prime 14969 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 14969 14968 1 3 [2, 2, 2, 1871]
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
    · apply IsUnit.of_mul_eq_one (7484 : ZMod 14969)
      decide
    · apply IsUnit.of_mul_eq_one (9472 : ZMod 14969)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_14983 : Nat.Prime 14983 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 14983 14982 1 3 [2, 3, 11, 227]
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
    · apply IsUnit.of_mul_eq_one (7491 : ZMod 14983)
      decide
    · apply IsUnit.of_mul_eq_one (885 : ZMod 14983)
      decide
    · apply IsUnit.of_mul_eq_one (14901 : ZMod 14983)
      decide
    · apply IsUnit.of_mul_eq_one (4244 : ZMod 14983)
      decide
  · norm_num
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_14051_14766_part02 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_14764 (p := 14149) (q := 14153) (by exact lowPrime_14153) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14764 (p := 14153) (q := 14159) (by exact lowPrime_14159) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14764 (p := 14159) (q := 14173) (by exact lowPrime_14173) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14764 (p := 14173) (q := 14177) (by exact lowPrime_14177) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14764 (p := 14177) (q := 14197) (by exact lowPrime_14197) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14764 (p := 14197) (q := 14207) (by exact lowPrime_14207) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14764 (p := 14207) (q := 14221) (by exact lowPrime_14221) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14764 (p := 14221) (q := 14243) (by exact lowPrime_14243) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_14051_14766_part02_chain :
    DusartPrimeRowsChain 14149 14242 dusartPrimeRows_14051_14766_part02 := by
  apply DusartPrimeRowsChain.cons
  · norm_num [dusartPrimeRow_of_explicit_14764]
  · norm_num [dusartPrimeRow_of_explicit_14764]
  · apply DusartPrimeRowsChain.cons
    · norm_num [dusartPrimeRow_of_explicit_14764]
    · norm_num [dusartPrimeRow_of_explicit_14764]
    · apply DusartPrimeRowsChain.cons
      · norm_num [dusartPrimeRow_of_explicit_14764]
      · norm_num [dusartPrimeRow_of_explicit_14764]
      · apply DusartPrimeRowsChain.cons
        · norm_num [dusartPrimeRow_of_explicit_14764]
        · norm_num [dusartPrimeRow_of_explicit_14764]
        · apply DusartPrimeRowsChain.cons
          · norm_num [dusartPrimeRow_of_explicit_14764]
          · norm_num [dusartPrimeRow_of_explicit_14764]
          · apply DusartPrimeRowsChain.cons
            · norm_num [dusartPrimeRow_of_explicit_14764]
            · norm_num [dusartPrimeRow_of_explicit_14764]
            · apply DusartPrimeRowsChain.cons
              · norm_num [dusartPrimeRow_of_explicit_14764]
              · norm_num [dusartPrimeRow_of_explicit_14764]
              · apply DusartPrimeRowsChain.cons
                · norm_num [dusartPrimeRow_of_explicit_14764]
                · norm_num [dusartPrimeRow_of_explicit_14764]
                · apply DusartPrimeRowsChain.empty
                  norm_num [dusartPrimeRow_of_explicit_14764, dusartPrimeRow_of_explicit_right]

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_14051_14766_part03 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_14764 (p := 14243) (q := 14249) (by exact lowPrime_14249) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14764 (p := 14249) (q := 14251) (by exact lowPrime_14251) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14764 (p := 14251) (q := 14281) (by exact lowPrime_14281) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14764 (p := 14281) (q := 14293) (by exact lowPrime_14293) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14764 (p := 14293) (q := 14303) (by exact lowPrime_14303) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14764 (p := 14303) (q := 14321) (by exact lowPrime_14321) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14764 (p := 14321) (q := 14323) (by exact lowPrime_14323) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14764 (p := 14323) (q := 14327) (by exact lowPrime_14327) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_14051_14766_part03_chain :
    DusartPrimeRowsChain 14243 14326 dusartPrimeRows_14051_14766_part03 := by
  apply DusartPrimeRowsChain.cons
  · norm_num [dusartPrimeRow_of_explicit_14764]
  · norm_num [dusartPrimeRow_of_explicit_14764]
  · apply DusartPrimeRowsChain.cons
    · norm_num [dusartPrimeRow_of_explicit_14764]
    · norm_num [dusartPrimeRow_of_explicit_14764]
    · apply DusartPrimeRowsChain.cons
      · norm_num [dusartPrimeRow_of_explicit_14764]
      · norm_num [dusartPrimeRow_of_explicit_14764]
      · apply DusartPrimeRowsChain.cons
        · norm_num [dusartPrimeRow_of_explicit_14764]
        · norm_num [dusartPrimeRow_of_explicit_14764]
        · apply DusartPrimeRowsChain.cons
          · norm_num [dusartPrimeRow_of_explicit_14764]
          · norm_num [dusartPrimeRow_of_explicit_14764]
          · apply DusartPrimeRowsChain.cons
            · norm_num [dusartPrimeRow_of_explicit_14764]
            · norm_num [dusartPrimeRow_of_explicit_14764]
            · apply DusartPrimeRowsChain.cons
              · norm_num [dusartPrimeRow_of_explicit_14764]
              · norm_num [dusartPrimeRow_of_explicit_14764]
              · apply DusartPrimeRowsChain.cons
                · norm_num [dusartPrimeRow_of_explicit_14764]
                · norm_num [dusartPrimeRow_of_explicit_14764]
                · apply DusartPrimeRowsChain.empty
                  norm_num [dusartPrimeRow_of_explicit_14764, dusartPrimeRow_of_explicit_right]

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_14051_14766_part04 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_14764 (p := 14327) (q := 14341) (by exact lowPrime_14341) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14764 (p := 14341) (q := 14347) (by exact lowPrime_14347) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14764 (p := 14347) (q := 14369) (by exact lowPrime_14369) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14764 (p := 14369) (q := 14387) (by exact lowPrime_14387) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14764 (p := 14387) (q := 14389) (by exact lowPrime_14389) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14764 (p := 14389) (q := 14401) (by exact lowPrime_14401) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14764 (p := 14401) (q := 14407) (by exact lowPrime_14407) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14764 (p := 14407) (q := 14411) (by exact lowPrime_14411) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_14051_14766_part04_chain :
    DusartPrimeRowsChain 14327 14410 dusartPrimeRows_14051_14766_part04 := by
  apply DusartPrimeRowsChain.cons
  · norm_num [dusartPrimeRow_of_explicit_14764]
  · norm_num [dusartPrimeRow_of_explicit_14764]
  · apply DusartPrimeRowsChain.cons
    · norm_num [dusartPrimeRow_of_explicit_14764]
    · norm_num [dusartPrimeRow_of_explicit_14764]
    · apply DusartPrimeRowsChain.cons
      · norm_num [dusartPrimeRow_of_explicit_14764]
      · norm_num [dusartPrimeRow_of_explicit_14764]
      · apply DusartPrimeRowsChain.cons
        · norm_num [dusartPrimeRow_of_explicit_14764]
        · norm_num [dusartPrimeRow_of_explicit_14764]
        · apply DusartPrimeRowsChain.cons
          · norm_num [dusartPrimeRow_of_explicit_14764]
          · norm_num [dusartPrimeRow_of_explicit_14764]
          · apply DusartPrimeRowsChain.cons
            · norm_num [dusartPrimeRow_of_explicit_14764]
            · norm_num [dusartPrimeRow_of_explicit_14764]
            · apply DusartPrimeRowsChain.cons
              · norm_num [dusartPrimeRow_of_explicit_14764]
              · norm_num [dusartPrimeRow_of_explicit_14764]
              · apply DusartPrimeRowsChain.cons
                · norm_num [dusartPrimeRow_of_explicit_14764]
                · norm_num [dusartPrimeRow_of_explicit_14764]
                · apply DusartPrimeRowsChain.empty
                  norm_num [dusartPrimeRow_of_explicit_14764, dusartPrimeRow_of_explicit_right]

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_14051_14766_part05 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_14764 (p := 14411) (q := 14419) (by exact lowPrime_14419) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14764 (p := 14419) (q := 14423) (by exact lowPrime_14423) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14764 (p := 14423) (q := 14431) (by exact lowPrime_14431) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14764 (p := 14431) (q := 14437) (by exact lowPrime_14437) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14764 (p := 14437) (q := 14447) (by exact lowPrime_14447) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14764 (p := 14447) (q := 14449) (by exact lowPrime_14449) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14764 (p := 14449) (q := 14461) (by exact lowPrime_14461) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14764 (p := 14461) (q := 14479) (by exact lowPrime_14479) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_14051_14766_part05_chain :
    DusartPrimeRowsChain 14411 14478 dusartPrimeRows_14051_14766_part05 := by
  apply DusartPrimeRowsChain.cons
  · norm_num [dusartPrimeRow_of_explicit_14764]
  · norm_num [dusartPrimeRow_of_explicit_14764]
  · apply DusartPrimeRowsChain.cons
    · norm_num [dusartPrimeRow_of_explicit_14764]
    · norm_num [dusartPrimeRow_of_explicit_14764]
    · apply DusartPrimeRowsChain.cons
      · norm_num [dusartPrimeRow_of_explicit_14764]
      · norm_num [dusartPrimeRow_of_explicit_14764]
      · apply DusartPrimeRowsChain.cons
        · norm_num [dusartPrimeRow_of_explicit_14764]
        · norm_num [dusartPrimeRow_of_explicit_14764]
        · apply DusartPrimeRowsChain.cons
          · norm_num [dusartPrimeRow_of_explicit_14764]
          · norm_num [dusartPrimeRow_of_explicit_14764]
          · apply DusartPrimeRowsChain.cons
            · norm_num [dusartPrimeRow_of_explicit_14764]
            · norm_num [dusartPrimeRow_of_explicit_14764]
            · apply DusartPrimeRowsChain.cons
              · norm_num [dusartPrimeRow_of_explicit_14764]
              · norm_num [dusartPrimeRow_of_explicit_14764]
              · apply DusartPrimeRowsChain.cons
                · norm_num [dusartPrimeRow_of_explicit_14764]
                · norm_num [dusartPrimeRow_of_explicit_14764]
                · apply DusartPrimeRowsChain.empty
                  norm_num [dusartPrimeRow_of_explicit_14764, dusartPrimeRow_of_explicit_right]

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_14051_14766_part06 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_14764 (p := 14479) (q := 14489) (by exact lowPrime_14489) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14764 (p := 14489) (q := 14503) (by exact lowPrime_14503) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14764 (p := 14503) (q := 14519) (by exact lowPrime_14519) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14764 (p := 14519) (q := 14533) (by exact lowPrime_14533) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14764 (p := 14533) (q := 14537) (by exact lowPrime_14537) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14764 (p := 14537) (q := 14543) (by exact lowPrime_14543) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14764 (p := 14543) (q := 14549) (by exact lowPrime_14549) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14764 (p := 14549) (q := 14551) (by exact lowPrime_14551) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_14051_14766_part06_chain :
    DusartPrimeRowsChain 14479 14550 dusartPrimeRows_14051_14766_part06 := by
  apply DusartPrimeRowsChain.cons
  · norm_num [dusartPrimeRow_of_explicit_14764]
  · norm_num [dusartPrimeRow_of_explicit_14764]
  · apply DusartPrimeRowsChain.cons
    · norm_num [dusartPrimeRow_of_explicit_14764]
    · norm_num [dusartPrimeRow_of_explicit_14764]
    · apply DusartPrimeRowsChain.cons
      · norm_num [dusartPrimeRow_of_explicit_14764]
      · norm_num [dusartPrimeRow_of_explicit_14764]
      · apply DusartPrimeRowsChain.cons
        · norm_num [dusartPrimeRow_of_explicit_14764]
        · norm_num [dusartPrimeRow_of_explicit_14764]
        · apply DusartPrimeRowsChain.cons
          · norm_num [dusartPrimeRow_of_explicit_14764]
          · norm_num [dusartPrimeRow_of_explicit_14764]
          · apply DusartPrimeRowsChain.cons
            · norm_num [dusartPrimeRow_of_explicit_14764]
            · norm_num [dusartPrimeRow_of_explicit_14764]
            · apply DusartPrimeRowsChain.cons
              · norm_num [dusartPrimeRow_of_explicit_14764]
              · norm_num [dusartPrimeRow_of_explicit_14764]
              · apply DusartPrimeRowsChain.cons
                · norm_num [dusartPrimeRow_of_explicit_14764]
                · norm_num [dusartPrimeRow_of_explicit_14764]
                · apply DusartPrimeRowsChain.empty
                  norm_num [dusartPrimeRow_of_explicit_14764, dusartPrimeRow_of_explicit_right]

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_14051_14766_part07 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_14764 (p := 14551) (q := 14557) (by exact lowPrime_14557) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14764 (p := 14557) (q := 14561) (by exact lowPrime_14561) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14764 (p := 14561) (q := 14563) (by exact lowPrime_14563) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14764 (p := 14563) (q := 14591) (by exact lowPrime_14591) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14764 (p := 14591) (q := 14593) (by exact lowPrime_14593) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14764 (p := 14593) (q := 14621) (by exact lowPrime_14621) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14764 (p := 14621) (q := 14627) (by exact lowPrime_14627) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14764 (p := 14627) (q := 14629) (by exact lowPrime_14629) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_14051_14766_part07_chain :
    DusartPrimeRowsChain 14551 14628 dusartPrimeRows_14051_14766_part07 := by
  apply DusartPrimeRowsChain.cons
  · norm_num [dusartPrimeRow_of_explicit_14764]
  · norm_num [dusartPrimeRow_of_explicit_14764]
  · apply DusartPrimeRowsChain.cons
    · norm_num [dusartPrimeRow_of_explicit_14764]
    · norm_num [dusartPrimeRow_of_explicit_14764]
    · apply DusartPrimeRowsChain.cons
      · norm_num [dusartPrimeRow_of_explicit_14764]
      · norm_num [dusartPrimeRow_of_explicit_14764]
      · apply DusartPrimeRowsChain.cons
        · norm_num [dusartPrimeRow_of_explicit_14764]
        · norm_num [dusartPrimeRow_of_explicit_14764]
        · apply DusartPrimeRowsChain.cons
          · norm_num [dusartPrimeRow_of_explicit_14764]
          · norm_num [dusartPrimeRow_of_explicit_14764]
          · apply DusartPrimeRowsChain.cons
            · norm_num [dusartPrimeRow_of_explicit_14764]
            · norm_num [dusartPrimeRow_of_explicit_14764]
            · apply DusartPrimeRowsChain.cons
              · norm_num [dusartPrimeRow_of_explicit_14764]
              · norm_num [dusartPrimeRow_of_explicit_14764]
              · apply DusartPrimeRowsChain.cons
                · norm_num [dusartPrimeRow_of_explicit_14764]
                · norm_num [dusartPrimeRow_of_explicit_14764]
                · apply DusartPrimeRowsChain.empty
                  norm_num [dusartPrimeRow_of_explicit_14764, dusartPrimeRow_of_explicit_right]

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_14051_14766_part08 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_14764 (p := 14629) (q := 14633) (by exact lowPrime_14633) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14764 (p := 14633) (q := 14639) (by exact lowPrime_14639) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14764 (p := 14639) (q := 14653) (by exact lowPrime_14653) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14764 (p := 14653) (q := 14657) (by exact lowPrime_14657) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14764 (p := 14657) (q := 14669) (by exact lowPrime_14669) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14764 (p := 14669) (q := 14683) (by exact lowPrime_14683) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14764 (p := 14683) (q := 14699) (by exact lowPrime_14699) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14764 (p := 14699) (q := 14713) (by exact lowPrime_14713) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_14051_14766_part08_chain :
    DusartPrimeRowsChain 14629 14712 dusartPrimeRows_14051_14766_part08 := by
  apply DusartPrimeRowsChain.cons
  · norm_num [dusartPrimeRow_of_explicit_14764]
  · norm_num [dusartPrimeRow_of_explicit_14764]
  · apply DusartPrimeRowsChain.cons
    · norm_num [dusartPrimeRow_of_explicit_14764]
    · norm_num [dusartPrimeRow_of_explicit_14764]
    · apply DusartPrimeRowsChain.cons
      · norm_num [dusartPrimeRow_of_explicit_14764]
      · norm_num [dusartPrimeRow_of_explicit_14764]
      · apply DusartPrimeRowsChain.cons
        · norm_num [dusartPrimeRow_of_explicit_14764]
        · norm_num [dusartPrimeRow_of_explicit_14764]
        · apply DusartPrimeRowsChain.cons
          · norm_num [dusartPrimeRow_of_explicit_14764]
          · norm_num [dusartPrimeRow_of_explicit_14764]
          · apply DusartPrimeRowsChain.cons
            · norm_num [dusartPrimeRow_of_explicit_14764]
            · norm_num [dusartPrimeRow_of_explicit_14764]
            · apply DusartPrimeRowsChain.cons
              · norm_num [dusartPrimeRow_of_explicit_14764]
              · norm_num [dusartPrimeRow_of_explicit_14764]
              · apply DusartPrimeRowsChain.cons
                · norm_num [dusartPrimeRow_of_explicit_14764]
                · norm_num [dusartPrimeRow_of_explicit_14764]
                · apply DusartPrimeRowsChain.empty
                  norm_num [dusartPrimeRow_of_explicit_14764, dusartPrimeRow_of_explicit_right]

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_14051_14766_part09 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_14764 (p := 14713) (q := 14717) (by exact lowPrime_14717) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14764 (p := 14717) (q := 14723) (by exact lowPrime_14723) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14764 (p := 14723) (q := 14731) (by exact lowPrime_14731) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14764 (p := 14731) (q := 14737) (by exact lowPrime_14737) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14764 (p := 14737) (q := 14741) (by exact lowPrime_14741) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14764 (p := 14741) (q := 14747) (by exact lowPrime_14747) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14764 (p := 14747) (q := 14753) (by exact lowPrime_14753) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14764 (p := 14753) (q := 14759) (by exact lowPrime_14759) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_14051_14766_part09_chain :
    DusartPrimeRowsChain 14713 14758 dusartPrimeRows_14051_14766_part09 := by
  apply DusartPrimeRowsChain.cons
  · norm_num [dusartPrimeRow_of_explicit_14764]
  · norm_num [dusartPrimeRow_of_explicit_14764]
  · apply DusartPrimeRowsChain.cons
    · norm_num [dusartPrimeRow_of_explicit_14764]
    · norm_num [dusartPrimeRow_of_explicit_14764]
    · apply DusartPrimeRowsChain.cons
      · norm_num [dusartPrimeRow_of_explicit_14764]
      · norm_num [dusartPrimeRow_of_explicit_14764]
      · apply DusartPrimeRowsChain.cons
        · norm_num [dusartPrimeRow_of_explicit_14764]
        · norm_num [dusartPrimeRow_of_explicit_14764]
        · apply DusartPrimeRowsChain.cons
          · norm_num [dusartPrimeRow_of_explicit_14764]
          · norm_num [dusartPrimeRow_of_explicit_14764]
          · apply DusartPrimeRowsChain.cons
            · norm_num [dusartPrimeRow_of_explicit_14764]
            · norm_num [dusartPrimeRow_of_explicit_14764]
            · apply DusartPrimeRowsChain.cons
              · norm_num [dusartPrimeRow_of_explicit_14764]
              · norm_num [dusartPrimeRow_of_explicit_14764]
              · apply DusartPrimeRowsChain.cons
                · norm_num [dusartPrimeRow_of_explicit_14764]
                · norm_num [dusartPrimeRow_of_explicit_14764]
                · apply DusartPrimeRowsChain.empty
                  norm_num [dusartPrimeRow_of_explicit_14764, dusartPrimeRow_of_explicit_right]

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_14051_14766_part10 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_14764 (p := 14759) (q := 14767) (by exact lowPrime_14767) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_14051_14766_part10_chain :
    DusartPrimeRowsChain 14759 14766 dusartPrimeRows_14051_14766_part10 := by
  apply DusartPrimeRowsChain.cons
  · norm_num [dusartPrimeRow_of_explicit_14764]
  · norm_num [dusartPrimeRow_of_explicit_14764]
  · apply DusartPrimeRowsChain.empty
    norm_num [dusartPrimeRow_of_explicit_14764, dusartPrimeRow_of_explicit_right]

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_14767_15526_part01 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_15521 (p := 14767) (q := 14771) (by exact lowPrime_14771) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_15521 (p := 14771) (q := 14779) (by exact lowPrime_14779) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_15521 (p := 14779) (q := 14783) (by exact lowPrime_14783) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_15521 (p := 14783) (q := 14797) (by exact lowPrime_14797) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_15521 (p := 14797) (q := 14813) (by exact lowPrime_14813) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_15521 (p := 14813) (q := 14821) (by exact lowPrime_14821) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_15521 (p := 14821) (q := 14827) (by exact lowPrime_14827) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_15521 (p := 14827) (q := 14831) (by exact lowPrime_14831) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_14767_15526_part01_chain :
    DusartPrimeRowsChain 14767 14830 dusartPrimeRows_14767_15526_part01 := by
  apply DusartPrimeRowsChain.cons
  · norm_num [dusartPrimeRow_of_explicit_15521]
  · norm_num [dusartPrimeRow_of_explicit_15521]
  · apply DusartPrimeRowsChain.cons
    · norm_num [dusartPrimeRow_of_explicit_15521]
    · norm_num [dusartPrimeRow_of_explicit_15521]
    · apply DusartPrimeRowsChain.cons
      · norm_num [dusartPrimeRow_of_explicit_15521]
      · norm_num [dusartPrimeRow_of_explicit_15521]
      · apply DusartPrimeRowsChain.cons
        · norm_num [dusartPrimeRow_of_explicit_15521]
        · norm_num [dusartPrimeRow_of_explicit_15521]
        · apply DusartPrimeRowsChain.cons
          · norm_num [dusartPrimeRow_of_explicit_15521]
          · norm_num [dusartPrimeRow_of_explicit_15521]
          · apply DusartPrimeRowsChain.cons
            · norm_num [dusartPrimeRow_of_explicit_15521]
            · norm_num [dusartPrimeRow_of_explicit_15521]
            · apply DusartPrimeRowsChain.cons
              · norm_num [dusartPrimeRow_of_explicit_15521]
              · norm_num [dusartPrimeRow_of_explicit_15521]
              · apply DusartPrimeRowsChain.cons
                · norm_num [dusartPrimeRow_of_explicit_15521]
                · norm_num [dusartPrimeRow_of_explicit_15521]
                · apply DusartPrimeRowsChain.empty
                  norm_num [dusartPrimeRow_of_explicit_15521, dusartPrimeRow_of_explicit_right]

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_14767_15526_part02 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_15521 (p := 14831) (q := 14843) (by exact lowPrime_14843) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_15521 (p := 14843) (q := 14851) (by exact lowPrime_14851) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_15521 (p := 14851) (q := 14867) (by exact lowPrime_14867) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_15521 (p := 14867) (q := 14869) (by exact lowPrime_14869) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_15521 (p := 14869) (q := 14879) (by exact lowPrime_14879) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_15521 (p := 14879) (q := 14887) (by exact lowPrime_14887) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_15521 (p := 14887) (q := 14891) (by exact lowPrime_14891) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_15521 (p := 14891) (q := 14897) (by exact lowPrime_14897) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_14767_15526_part02_chain :
    DusartPrimeRowsChain 14831 14896 dusartPrimeRows_14767_15526_part02 := by
  apply DusartPrimeRowsChain.cons
  · norm_num [dusartPrimeRow_of_explicit_15521]
  · norm_num [dusartPrimeRow_of_explicit_15521]
  · apply DusartPrimeRowsChain.cons
    · norm_num [dusartPrimeRow_of_explicit_15521]
    · norm_num [dusartPrimeRow_of_explicit_15521]
    · apply DusartPrimeRowsChain.cons
      · norm_num [dusartPrimeRow_of_explicit_15521]
      · norm_num [dusartPrimeRow_of_explicit_15521]
      · apply DusartPrimeRowsChain.cons
        · norm_num [dusartPrimeRow_of_explicit_15521]
        · norm_num [dusartPrimeRow_of_explicit_15521]
        · apply DusartPrimeRowsChain.cons
          · norm_num [dusartPrimeRow_of_explicit_15521]
          · norm_num [dusartPrimeRow_of_explicit_15521]
          · apply DusartPrimeRowsChain.cons
            · norm_num [dusartPrimeRow_of_explicit_15521]
            · norm_num [dusartPrimeRow_of_explicit_15521]
            · apply DusartPrimeRowsChain.cons
              · norm_num [dusartPrimeRow_of_explicit_15521]
              · norm_num [dusartPrimeRow_of_explicit_15521]
              · apply DusartPrimeRowsChain.cons
                · norm_num [dusartPrimeRow_of_explicit_15521]
                · norm_num [dusartPrimeRow_of_explicit_15521]
                · apply DusartPrimeRowsChain.empty
                  norm_num [dusartPrimeRow_of_explicit_15521, dusartPrimeRow_of_explicit_right]

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_14767_15526_part03 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_15521 (p := 14897) (q := 14923) (by exact lowPrime_14923) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_15521 (p := 14923) (q := 14929) (by exact lowPrime_14929) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_15521 (p := 14929) (q := 14939) (by exact lowPrime_14939) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_15521 (p := 14939) (q := 14947) (by exact lowPrime_14947) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_15521 (p := 14947) (q := 14951) (by exact lowPrime_14951) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_15521 (p := 14951) (q := 14957) (by exact lowPrime_14957) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_15521 (p := 14957) (q := 14969) (by exact lowPrime_14969) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_15521 (p := 14969) (q := 14983) (by exact lowPrime_14983) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_14767_15526_part03_chain :
    DusartPrimeRowsChain 14897 14982 dusartPrimeRows_14767_15526_part03 := by
  apply DusartPrimeRowsChain.cons
  · norm_num [dusartPrimeRow_of_explicit_15521]
  · norm_num [dusartPrimeRow_of_explicit_15521]
  · apply DusartPrimeRowsChain.cons
    · norm_num [dusartPrimeRow_of_explicit_15521]
    · norm_num [dusartPrimeRow_of_explicit_15521]
    · apply DusartPrimeRowsChain.cons
      · norm_num [dusartPrimeRow_of_explicit_15521]
      · norm_num [dusartPrimeRow_of_explicit_15521]
      · apply DusartPrimeRowsChain.cons
        · norm_num [dusartPrimeRow_of_explicit_15521]
        · norm_num [dusartPrimeRow_of_explicit_15521]
        · apply DusartPrimeRowsChain.cons
          · norm_num [dusartPrimeRow_of_explicit_15521]
          · norm_num [dusartPrimeRow_of_explicit_15521]
          · apply DusartPrimeRowsChain.cons
            · norm_num [dusartPrimeRow_of_explicit_15521]
            · norm_num [dusartPrimeRow_of_explicit_15521]
            · apply DusartPrimeRowsChain.cons
              · norm_num [dusartPrimeRow_of_explicit_15521]
              · norm_num [dusartPrimeRow_of_explicit_15521]
              · apply DusartPrimeRowsChain.cons
                · norm_num [dusartPrimeRow_of_explicit_15521]
                · norm_num [dusartPrimeRow_of_explicit_15521]
                · apply DusartPrimeRowsChain.empty
                  norm_num [dusartPrimeRow_of_explicit_15521, dusartPrimeRow_of_explicit_right]
