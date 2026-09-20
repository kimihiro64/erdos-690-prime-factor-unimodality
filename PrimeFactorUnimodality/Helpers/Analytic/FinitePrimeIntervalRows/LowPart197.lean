import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowBase

set_option autoImplicit false
set_option maxRecDepth 1000000

/-! # Lower finite Dusart prefix chunk 197 -/

namespace PrimeFactorUnimodality

noncomputable section
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_16651 : Nat.Prime 16651 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 16651 16650 1 2 [2, 3, 3, 5, 5, 37]
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
    · apply IsUnit.of_mul_eq_one (8325 : ZMod 16651)
      decide
    · apply IsUnit.of_mul_eq_one (16576 : ZMod 16651)
      decide
    · apply IsUnit.of_mul_eq_one (7823 : ZMod 16651)
      decide
    · apply IsUnit.of_mul_eq_one (7201 : ZMod 16651)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_16657 : Nat.Prime 16657 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 16657 16656 1 5 [2, 2, 2, 2, 3, 347]
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
    · apply IsUnit.of_mul_eq_one (8328 : ZMod 16657)
      decide
    · apply IsUnit.of_mul_eq_one (13340 : ZMod 16657)
      decide
    · apply IsUnit.of_mul_eq_one (13230 : ZMod 16657)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_16661 : Nat.Prime 16661 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 16661 16660 1 10 [2, 2, 5, 7, 7, 17]
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
    · apply IsUnit.of_mul_eq_one (8330 : ZMod 16661)
      decide
    · apply IsUnit.of_mul_eq_one (4536 : ZMod 16661)
      decide
    · apply IsUnit.of_mul_eq_one (7229 : ZMod 16661)
      decide
    · apply IsUnit.of_mul_eq_one (13012 : ZMod 16661)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_16673 : Nat.Prime 16673 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 16673 16672 1 3 [2, 2, 2, 2, 2, 521]
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
    · apply IsUnit.of_mul_eq_one (8336 : ZMod 16673)
      decide
    · apply IsUnit.of_mul_eq_one (5471 : ZMod 16673)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_16691 : Nat.Prime 16691 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 16691 16690 1 6 [2, 5, 1669]
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
    · apply IsUnit.of_mul_eq_one (8345 : ZMod 16691)
      decide
    · apply IsUnit.of_mul_eq_one (145 : ZMod 16691)
      decide
    · apply IsUnit.of_mul_eq_one (7768 : ZMod 16691)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_16693 : Nat.Prime 16693 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 16693 16692 1 2 [2, 2, 3, 13, 107]
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
    · apply IsUnit.of_mul_eq_one (8346 : ZMod 16693)
      decide
    · apply IsUnit.of_mul_eq_one (3846 : ZMod 16693)
      decide
    · apply IsUnit.of_mul_eq_one (2840 : ZMod 16693)
      decide
    · apply IsUnit.of_mul_eq_one (15373 : ZMod 16693)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_16699 : Nat.Prime 16699 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 16699 16698 1 3 [2, 3, 11, 11, 23]
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
    · apply IsUnit.of_mul_eq_one (8349 : ZMod 16699)
      decide
    · apply IsUnit.of_mul_eq_one (4107 : ZMod 16699)
      decide
    · apply IsUnit.of_mul_eq_one (8096 : ZMod 16699)
      decide
    · apply IsUnit.of_mul_eq_one (5182 : ZMod 16699)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_16703 : Nat.Prime 16703 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 16703 16702 1 5 [2, 7, 1193]
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
    · apply IsUnit.of_mul_eq_one (8351 : ZMod 16703)
      decide
    · apply IsUnit.of_mul_eq_one (4805 : ZMod 16703)
      decide
    · apply IsUnit.of_mul_eq_one (10488 : ZMod 16703)
      decide
  · norm_num
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_16319_17158_part05 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_17154 (p := 16649) (q := 16651) (by exact lowPrime_16651) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_17154 (p := 16651) (q := 16657) (by exact lowPrime_16657) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_17154 (p := 16657) (q := 16661) (by exact lowPrime_16661) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_17154 (p := 16661) (q := 16673) (by exact lowPrime_16673) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_17154 (p := 16673) (q := 16691) (by exact lowPrime_16691) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_17154 (p := 16691) (q := 16693) (by exact lowPrime_16693) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_17154 (p := 16693) (q := 16699) (by exact lowPrime_16699) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_17154 (p := 16699) (q := 16703) (by exact lowPrime_16703) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_16319_17158_part05_chain :
    DusartPrimeRowsChain 16649 16702 dusartPrimeRows_16319_17158_part05 := by
  apply DusartPrimeRowsChain.cons
  · norm_num [dusartPrimeRow_of_explicit_17154]
  · norm_num [dusartPrimeRow_of_explicit_17154]
  · apply DusartPrimeRowsChain.cons
    · norm_num [dusartPrimeRow_of_explicit_17154]
    · norm_num [dusartPrimeRow_of_explicit_17154]
    · apply DusartPrimeRowsChain.cons
      · norm_num [dusartPrimeRow_of_explicit_17154]
      · norm_num [dusartPrimeRow_of_explicit_17154]
      · apply DusartPrimeRowsChain.cons
        · norm_num [dusartPrimeRow_of_explicit_17154]
        · norm_num [dusartPrimeRow_of_explicit_17154]
        · apply DusartPrimeRowsChain.cons
          · norm_num [dusartPrimeRow_of_explicit_17154]
          · norm_num [dusartPrimeRow_of_explicit_17154]
          · apply DusartPrimeRowsChain.cons
            · norm_num [dusartPrimeRow_of_explicit_17154]
            · norm_num [dusartPrimeRow_of_explicit_17154]
            · apply DusartPrimeRowsChain.cons
              · norm_num [dusartPrimeRow_of_explicit_17154]
              · norm_num [dusartPrimeRow_of_explicit_17154]
              · apply DusartPrimeRowsChain.cons
                · norm_num [dusartPrimeRow_of_explicit_17154]
                · norm_num [dusartPrimeRow_of_explicit_17154]
                · apply DusartPrimeRowsChain.empty
                  norm_num [dusartPrimeRow_of_explicit_17154, dusartPrimeRow_of_explicit_right]
