import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowBase

set_option autoImplicit false
set_option maxRecDepth 1000000

/-! # Lower finite Dusart prefix chunk 267 -/

namespace PrimeFactorUnimodality

noncomputable section
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
