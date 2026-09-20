import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowBase

set_option autoImplicit false
set_option maxRecDepth 1000000

/-! # Lower finite Dusart prefix chunk 154 -/

namespace PrimeFactorUnimodality

noncomputable section
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_13537 : Nat.Prime 13537 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 13537 13536 1 7 [2, 2, 2, 2, 2, 3, 3, 47]
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
    · apply IsUnit.of_mul_eq_one (6768 : ZMod 13537)
      decide
    · apply IsUnit.of_mul_eq_one (4372 : ZMod 13537)
      decide
    · apply IsUnit.of_mul_eq_one (10420 : ZMod 13537)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_13553 : Nat.Prime 13553 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 13553 13552 1 3 [2, 2, 2, 2, 7, 11, 11]
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
    · apply IsUnit.of_mul_eq_one (6776 : ZMod 13553)
      decide
    · apply IsUnit.of_mul_eq_one (13202 : ZMod 13553)
      decide
    · apply IsUnit.of_mul_eq_one (7638 : ZMod 13553)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_13567 : Nat.Prime 13567 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 13567 13566 1 3 [2, 3, 7, 17, 19]
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
    · apply IsUnit.of_mul_eq_one (6783 : ZMod 13567)
      decide
    · apply IsUnit.of_mul_eq_one (6108 : ZMod 13567)
      decide
    · apply IsUnit.of_mul_eq_one (11095 : ZMod 13567)
      decide
    · apply IsUnit.of_mul_eq_one (11924 : ZMod 13567)
      decide
    · apply IsUnit.of_mul_eq_one (1212 : ZMod 13567)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_13577 : Nat.Prime 13577 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 13577 13576 1 3 [2, 2, 2, 1697]
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
    · apply IsUnit.of_mul_eq_one (6788 : ZMod 13577)
      decide
    · apply IsUnit.of_mul_eq_one (7962 : ZMod 13577)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_13591 : Nat.Prime 13591 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 13591 13590 1 3 [2, 3, 3, 5, 151]
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
    · apply IsUnit.of_mul_eq_one (6795 : ZMod 13591)
      decide
    · apply IsUnit.of_mul_eq_one (3616 : ZMod 13591)
      decide
    · apply IsUnit.of_mul_eq_one (5994 : ZMod 13591)
      decide
    · apply IsUnit.of_mul_eq_one (3859 : ZMod 13591)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_13597 : Nat.Prime 13597 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 13597 13596 1 5 [2, 2, 3, 11, 103]
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
    · apply IsUnit.of_mul_eq_one (6798 : ZMod 13597)
      decide
    · apply IsUnit.of_mul_eq_one (12120 : ZMod 13597)
      decide
    · apply IsUnit.of_mul_eq_one (3813 : ZMod 13597)
      decide
    · apply IsUnit.of_mul_eq_one (5587 : ZMod 13597)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_13613 : Nat.Prime 13613 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 13613 13612 1 2 [2, 2, 41, 83]
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
    · apply IsUnit.of_mul_eq_one (6806 : ZMod 13613)
      decide
    · apply IsUnit.of_mul_eq_one (983 : ZMod 13613)
      decide
    · apply IsUnit.of_mul_eq_one (10062 : ZMod 13613)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_13619 : Nat.Prime 13619 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 13619 13618 1 2 [2, 11, 619]
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
    · apply IsUnit.of_mul_eq_one (6809 : ZMod 13619)
      decide
    · apply IsUnit.of_mul_eq_one (10229 : ZMod 13619)
      decide
    · apply IsUnit.of_mul_eq_one (5112 : ZMod 13619)
      decide
  · norm_num
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_13367_14050_part03 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_14044 (p := 13523) (q := 13537) (by exact lowPrime_13537) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14044 (p := 13537) (q := 13553) (by exact lowPrime_13553) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14044 (p := 13553) (q := 13567) (by exact lowPrime_13567) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14044 (p := 13567) (q := 13577) (by exact lowPrime_13577) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14044 (p := 13577) (q := 13591) (by exact lowPrime_13591) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14044 (p := 13591) (q := 13597) (by exact lowPrime_13597) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14044 (p := 13597) (q := 13613) (by exact lowPrime_13613) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14044 (p := 13613) (q := 13619) (by exact lowPrime_13619) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_13367_14050_part03_chain :
    DusartPrimeRowsChain 13523 13618 dusartPrimeRows_13367_14050_part03 := by
  apply DusartPrimeRowsChain.cons
  · norm_num [dusartPrimeRow_of_explicit_14044]
  · norm_num [dusartPrimeRow_of_explicit_14044]
  · apply DusartPrimeRowsChain.cons
    · norm_num [dusartPrimeRow_of_explicit_14044]
    · norm_num [dusartPrimeRow_of_explicit_14044]
    · apply DusartPrimeRowsChain.cons
      · norm_num [dusartPrimeRow_of_explicit_14044]
      · norm_num [dusartPrimeRow_of_explicit_14044]
      · apply DusartPrimeRowsChain.cons
        · norm_num [dusartPrimeRow_of_explicit_14044]
        · norm_num [dusartPrimeRow_of_explicit_14044]
        · apply DusartPrimeRowsChain.cons
          · norm_num [dusartPrimeRow_of_explicit_14044]
          · norm_num [dusartPrimeRow_of_explicit_14044]
          · apply DusartPrimeRowsChain.cons
            · norm_num [dusartPrimeRow_of_explicit_14044]
            · norm_num [dusartPrimeRow_of_explicit_14044]
            · apply DusartPrimeRowsChain.cons
              · norm_num [dusartPrimeRow_of_explicit_14044]
              · norm_num [dusartPrimeRow_of_explicit_14044]
              · apply DusartPrimeRowsChain.cons
                · norm_num [dusartPrimeRow_of_explicit_14044]
                · norm_num [dusartPrimeRow_of_explicit_14044]
                · apply DusartPrimeRowsChain.empty
                  norm_num [dusartPrimeRow_of_explicit_14044, dusartPrimeRow_of_explicit_right]
