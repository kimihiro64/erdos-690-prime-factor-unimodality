import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowBase

set_option autoImplicit false
set_option maxRecDepth 1000000

/-! # Lower finite Dusart prefix chunk 167 -/

namespace PrimeFactorUnimodality

noncomputable section
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
