import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowBase

set_option autoImplicit false
set_option maxRecDepth 1000000

/-! # Lower finite Dusart prefix chunk 168 -/

namespace PrimeFactorUnimodality

noncomputable section
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
