import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowBase

set_option autoImplicit false
set_option maxRecDepth 1000000

/-! # Lower finite Dusart prefix chunk 260 -/

namespace PrimeFactorUnimodality

noncomputable section
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
