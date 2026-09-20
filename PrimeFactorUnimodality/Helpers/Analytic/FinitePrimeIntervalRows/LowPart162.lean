import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowBase

set_option autoImplicit false
set_option maxRecDepth 1000000

/-! # Lower finite Dusart prefix chunk 162 -/

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
