import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowBase

set_option autoImplicit false
set_option maxRecDepth 1000000

/-! # Lower finite Dusart prefix chunk 243 -/

namespace PrimeFactorUnimodality

noncomputable section
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_20743 : Nat.Prime 20743 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 20743 20742 1 5 [2, 3, 3457]
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
    · apply IsUnit.of_mul_eq_one (10371 : ZMod 20743)
      decide
    · apply IsUnit.of_mul_eq_one (10261 : ZMod 20743)
      decide
    · apply IsUnit.of_mul_eq_one (2253 : ZMod 20743)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_20747 : Nat.Prime 20747 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 20747 20746 1 5 [2, 11, 23, 41]
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
    · apply IsUnit.of_mul_eq_one (10373 : ZMod 20747)
      decide
    · apply IsUnit.of_mul_eq_one (18178 : ZMod 20747)
      decide
    · apply IsUnit.of_mul_eq_one (12531 : ZMod 20747)
      decide
    · apply IsUnit.of_mul_eq_one (16397 : ZMod 20747)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_20749 : Nat.Prime 20749 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 20749 20748 1 2 [2, 2, 3, 7, 13, 19]
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
    · apply IsUnit.of_mul_eq_one (10374 : ZMod 20749)
      decide
    · apply IsUnit.of_mul_eq_one (5876 : ZMod 20749)
      decide
    · apply IsUnit.of_mul_eq_one (13870 : ZMod 20749)
      decide
    · apply IsUnit.of_mul_eq_one (1786 : ZMod 20749)
      decide
    · apply IsUnit.of_mul_eq_one (19932 : ZMod 20749)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_20753 : Nat.Prime 20753 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 20753 20752 1 3 [2, 2, 2, 2, 1297]
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
    · apply IsUnit.of_mul_eq_one (10376 : ZMod 20753)
      decide
    · apply IsUnit.of_mul_eq_one (7254 : ZMod 20753)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_20759 : Nat.Prime 20759 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 20759 20758 1 7 [2, 97, 107]
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
    · apply IsUnit.of_mul_eq_one (10379 : ZMod 20759)
      decide
    · apply IsUnit.of_mul_eq_one (15464 : ZMod 20759)
      decide
    · apply IsUnit.of_mul_eq_one (1218 : ZMod 20759)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_20771 : Nat.Prime 20771 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 20771 20770 1 2 [2, 5, 31, 67]
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
    · apply IsUnit.of_mul_eq_one (10385 : ZMod 20771)
      decide
    · apply IsUnit.of_mul_eq_one (13327 : ZMod 20771)
      decide
    · apply IsUnit.of_mul_eq_one (17947 : ZMod 20771)
      decide
    · apply IsUnit.of_mul_eq_one (7321 : ZMod 20771)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_20773 : Nat.Prime 20773 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 20773 20772 1 2 [2, 2, 3, 3, 577]
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
    · apply IsUnit.of_mul_eq_one (10386 : ZMod 20773)
      decide
    · apply IsUnit.of_mul_eq_one (7397 : ZMod 20773)
      decide
    · apply IsUnit.of_mul_eq_one (449 : ZMod 20773)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_20789 : Nat.Prime 20789 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 20789 20788 1 2 [2, 2, 5197]
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
    · apply IsUnit.of_mul_eq_one (10394 : ZMod 20789)
      decide
    · apply IsUnit.of_mul_eq_one (1386 : ZMod 20789)
      decide
  · norm_num
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_19937_20958_part11 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_20952 (p := 20731) (q := 20743) (by exact lowPrime_20743) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_20952 (p := 20743) (q := 20747) (by exact lowPrime_20747) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_20952 (p := 20747) (q := 20749) (by exact lowPrime_20749) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_20952 (p := 20749) (q := 20753) (by exact lowPrime_20753) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_20952 (p := 20753) (q := 20759) (by exact lowPrime_20759) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_20952 (p := 20759) (q := 20771) (by exact lowPrime_20771) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_20952 (p := 20771) (q := 20773) (by exact lowPrime_20773) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_20952 (p := 20773) (q := 20789) (by exact lowPrime_20789) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_19937_20958_part11_chain :
    DusartPrimeRowsChain 20731 20788 dusartPrimeRows_19937_20958_part11 := by
  apply DusartPrimeRowsChain.cons
  · norm_num [dusartPrimeRow_of_explicit_20952]
  · norm_num [dusartPrimeRow_of_explicit_20952]
  · apply DusartPrimeRowsChain.cons
    · norm_num [dusartPrimeRow_of_explicit_20952]
    · norm_num [dusartPrimeRow_of_explicit_20952]
    · apply DusartPrimeRowsChain.cons
      · norm_num [dusartPrimeRow_of_explicit_20952]
      · norm_num [dusartPrimeRow_of_explicit_20952]
      · apply DusartPrimeRowsChain.cons
        · norm_num [dusartPrimeRow_of_explicit_20952]
        · norm_num [dusartPrimeRow_of_explicit_20952]
        · apply DusartPrimeRowsChain.cons
          · norm_num [dusartPrimeRow_of_explicit_20952]
          · norm_num [dusartPrimeRow_of_explicit_20952]
          · apply DusartPrimeRowsChain.cons
            · norm_num [dusartPrimeRow_of_explicit_20952]
            · norm_num [dusartPrimeRow_of_explicit_20952]
            · apply DusartPrimeRowsChain.cons
              · norm_num [dusartPrimeRow_of_explicit_20952]
              · norm_num [dusartPrimeRow_of_explicit_20952]
              · apply DusartPrimeRowsChain.cons
                · norm_num [dusartPrimeRow_of_explicit_20952]
                · norm_num [dusartPrimeRow_of_explicit_20952]
                · apply DusartPrimeRowsChain.empty
                  norm_num [dusartPrimeRow_of_explicit_20952, dusartPrimeRow_of_explicit_right]
