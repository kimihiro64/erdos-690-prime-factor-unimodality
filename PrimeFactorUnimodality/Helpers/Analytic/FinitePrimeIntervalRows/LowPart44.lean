import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowBase

set_option autoImplicit false
set_option maxRecDepth 1000000

/-! # Lower finite Dusart prefix chunk 44 -/

namespace PrimeFactorUnimodality

noncomputable section
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_6011 : Nat.Prime 6011 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 6011 6010 1 2 [2, 5, 601]
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
    · apply IsUnit.of_mul_eq_one (3005 : ZMod 6011)
      decide
    · apply IsUnit.of_mul_eq_one (4877 : ZMod 6011)
      decide
    · apply IsUnit.of_mul_eq_one (852 : ZMod 6011)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_6029 : Nat.Prime 6029 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 6029 6028 1 2 [2, 2, 11, 137]
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
    · apply IsUnit.of_mul_eq_one (3014 : ZMod 6029)
      decide
    · apply IsUnit.of_mul_eq_one (1419 : ZMod 6029)
      decide
    · apply IsUnit.of_mul_eq_one (1592 : ZMod 6029)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_6037 : Nat.Prime 6037 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 6037 6036 1 5 [2, 2, 3, 503]
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
    · apply IsUnit.of_mul_eq_one (3018 : ZMod 6037)
      decide
    · apply IsUnit.of_mul_eq_one (4194 : ZMod 6037)
      decide
    · apply IsUnit.of_mul_eq_one (3384 : ZMod 6037)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_6043 : Nat.Prime 6043 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 6043 6042 1 5 [2, 3, 19, 53]
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
    · apply IsUnit.of_mul_eq_one (3021 : ZMod 6043)
      decide
    · apply IsUnit.of_mul_eq_one (1442 : ZMod 6043)
      decide
    · apply IsUnit.of_mul_eq_one (4832 : ZMod 6043)
      decide
    · apply IsUnit.of_mul_eq_one (3707 : ZMod 6043)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_6047 : Nat.Prime 6047 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 6047 6046 1 5 [2, 3023]
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
    · apply IsUnit.of_mul_eq_one (3023 : ZMod 6047)
      decide
    · apply IsUnit.of_mul_eq_one (252 : ZMod 6047)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_6053 : Nat.Prime 6053 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 6053 6052 1 2 [2, 2, 17, 89]
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
    · apply IsUnit.of_mul_eq_one (3026 : ZMod 6053)
      decide
    · apply IsUnit.of_mul_eq_one (1842 : ZMod 6053)
      decide
    · apply IsUnit.of_mul_eq_one (2982 : ZMod 6053)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_6067 : Nat.Prime 6067 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 6067 6066 1 2 [2, 3, 3, 337]
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
    · apply IsUnit.of_mul_eq_one (3033 : ZMod 6067)
      decide
    · apply IsUnit.of_mul_eq_one (1800 : ZMod 6067)
      decide
    · apply IsUnit.of_mul_eq_one (774 : ZMod 6067)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_6073 : Nat.Prime 6073 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 6073 6072 1 10 [2, 2, 2, 3, 11, 23]
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
    · apply IsUnit.of_mul_eq_one (3036 : ZMod 6073)
      decide
    · apply IsUnit.of_mul_eq_one (3434 : ZMod 6073)
      decide
    · apply IsUnit.of_mul_eq_one (5796 : ZMod 6073)
      decide
    · apply IsUnit.of_mul_eq_one (2188 : ZMod 6073)
      decide
  · norm_num
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_6007_6310_part01 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_6310 (p := 6007) (q := 6011) (by exact lowPrime_6011) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6310 (p := 6011) (q := 6029) (by exact lowPrime_6029) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6310 (p := 6029) (q := 6037) (by exact lowPrime_6037) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6310 (p := 6037) (q := 6043) (by exact lowPrime_6043) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6310 (p := 6043) (q := 6047) (by exact lowPrime_6047) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6310 (p := 6047) (q := 6053) (by exact lowPrime_6053) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6310 (p := 6053) (q := 6067) (by exact lowPrime_6067) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6310 (p := 6067) (q := 6073) (by exact lowPrime_6073) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_6007_6310_part01_chain :
    DusartPrimeRowsChain 6007 6072 dusartPrimeRows_6007_6310_part01 := by
  apply DusartPrimeRowsChain.cons
  · norm_num [dusartPrimeRow_of_explicit_6310]
  · norm_num [dusartPrimeRow_of_explicit_6310]
  · apply DusartPrimeRowsChain.cons
    · norm_num [dusartPrimeRow_of_explicit_6310]
    · norm_num [dusartPrimeRow_of_explicit_6310]
    · apply DusartPrimeRowsChain.cons
      · norm_num [dusartPrimeRow_of_explicit_6310]
      · norm_num [dusartPrimeRow_of_explicit_6310]
      · apply DusartPrimeRowsChain.cons
        · norm_num [dusartPrimeRow_of_explicit_6310]
        · norm_num [dusartPrimeRow_of_explicit_6310]
        · apply DusartPrimeRowsChain.cons
          · norm_num [dusartPrimeRow_of_explicit_6310]
          · norm_num [dusartPrimeRow_of_explicit_6310]
          · apply DusartPrimeRowsChain.cons
            · norm_num [dusartPrimeRow_of_explicit_6310]
            · norm_num [dusartPrimeRow_of_explicit_6310]
            · apply DusartPrimeRowsChain.cons
              · norm_num [dusartPrimeRow_of_explicit_6310]
              · norm_num [dusartPrimeRow_of_explicit_6310]
              · apply DusartPrimeRowsChain.cons
                · norm_num [dusartPrimeRow_of_explicit_6310]
                · norm_num [dusartPrimeRow_of_explicit_6310]
                · apply DusartPrimeRowsChain.empty
                  norm_num [dusartPrimeRow_of_explicit_6310, dusartPrimeRow_of_explicit_right]
