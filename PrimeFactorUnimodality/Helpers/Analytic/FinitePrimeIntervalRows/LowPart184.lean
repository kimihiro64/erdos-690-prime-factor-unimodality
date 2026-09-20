import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowBase

set_option autoImplicit false
set_option maxRecDepth 1000000

/-! # Lower finite Dusart prefix chunk 184 -/

namespace PrimeFactorUnimodality

noncomputable section
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_15671 : Nat.Prime 15671 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 15671 15670 1 13 [2, 5, 1567]
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
    · apply IsUnit.of_mul_eq_one (7835 : ZMod 15671)
      decide
    · apply IsUnit.of_mul_eq_one (2029 : ZMod 15671)
      decide
    · apply IsUnit.of_mul_eq_one (1400 : ZMod 15671)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_15679 : Nat.Prime 15679 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 15679 15678 1 11 [2, 3, 3, 13, 67]
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
    · apply IsUnit.of_mul_eq_one (7839 : ZMod 15679)
      decide
    · apply IsUnit.of_mul_eq_one (4239 : ZMod 15679)
      decide
    · apply IsUnit.of_mul_eq_one (14607 : ZMod 15679)
      decide
    · apply IsUnit.of_mul_eq_one (15173 : ZMod 15679)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_15683 : Nat.Prime 15683 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 15683 15682 1 2 [2, 7841]
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
    · apply IsUnit.of_mul_eq_one (7841 : ZMod 15683)
      decide
    · apply IsUnit.of_mul_eq_one (5228 : ZMod 15683)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_15727 : Nat.Prime 15727 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 15727 15726 1 3 [2, 3, 2621]
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
    · apply IsUnit.of_mul_eq_one (7863 : ZMod 15727)
      decide
    · apply IsUnit.of_mul_eq_one (13865 : ZMod 15727)
      decide
    · apply IsUnit.of_mul_eq_one (11428 : ZMod 15727)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_15731 : Nat.Prime 15731 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 15731 15730 1 2 [2, 5, 11, 11, 13]
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
    · apply IsUnit.of_mul_eq_one (7865 : ZMod 15731)
      decide
    · apply IsUnit.of_mul_eq_one (4097 : ZMod 15731)
      decide
    · apply IsUnit.of_mul_eq_one (3888 : ZMod 15731)
      decide
    · apply IsUnit.of_mul_eq_one (11175 : ZMod 15731)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_15733 : Nat.Prime 15733 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 15733 15732 1 6 [2, 2, 3, 3, 19, 23]
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
    · apply IsUnit.of_mul_eq_one (7866 : ZMod 15733)
      decide
    · apply IsUnit.of_mul_eq_one (15292 : ZMod 15733)
      decide
    · apply IsUnit.of_mul_eq_one (8699 : ZMod 15733)
      decide
    · apply IsUnit.of_mul_eq_one (5611 : ZMod 15733)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_15737 : Nat.Prime 15737 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 15737 15736 1 3 [2, 2, 2, 7, 281]
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
    · apply IsUnit.of_mul_eq_one (7868 : ZMod 15737)
      decide
    · apply IsUnit.of_mul_eq_one (13272 : ZMod 15737)
      decide
    · apply IsUnit.of_mul_eq_one (14919 : ZMod 15737)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_15739 : Nat.Prime 15739 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 15739 15738 1 2 [2, 3, 43, 61]
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
    · apply IsUnit.of_mul_eq_one (7869 : ZMod 15739)
      decide
    · apply IsUnit.of_mul_eq_one (8821 : ZMod 15739)
      decide
    · apply IsUnit.of_mul_eq_one (8607 : ZMod 15739)
      decide
    · apply IsUnit.of_mul_eq_one (7795 : ZMod 15739)
      decide
  · norm_num
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_15527_16318_part03 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_16317 (p := 15667) (q := 15671) (by exact lowPrime_15671) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_16317 (p := 15671) (q := 15679) (by exact lowPrime_15679) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_16317 (p := 15679) (q := 15683) (by exact lowPrime_15683) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_16317 (p := 15683) (q := 15727) (by exact lowPrime_15727) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_16317 (p := 15727) (q := 15731) (by exact lowPrime_15731) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_16317 (p := 15731) (q := 15733) (by exact lowPrime_15733) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_16317 (p := 15733) (q := 15737) (by exact lowPrime_15737) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_16317 (p := 15737) (q := 15739) (by exact lowPrime_15739) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_15527_16318_part03_chain :
    DusartPrimeRowsChain 15667 15738 dusartPrimeRows_15527_16318_part03 := by
  apply DusartPrimeRowsChain.cons
  · norm_num [dusartPrimeRow_of_explicit_16317]
  · norm_num [dusartPrimeRow_of_explicit_16317]
  · apply DusartPrimeRowsChain.cons
    · norm_num [dusartPrimeRow_of_explicit_16317]
    · norm_num [dusartPrimeRow_of_explicit_16317]
    · apply DusartPrimeRowsChain.cons
      · norm_num [dusartPrimeRow_of_explicit_16317]
      · norm_num [dusartPrimeRow_of_explicit_16317]
      · apply DusartPrimeRowsChain.cons
        · norm_num [dusartPrimeRow_of_explicit_16317]
        · norm_num [dusartPrimeRow_of_explicit_16317]
        · apply DusartPrimeRowsChain.cons
          · norm_num [dusartPrimeRow_of_explicit_16317]
          · norm_num [dusartPrimeRow_of_explicit_16317]
          · apply DusartPrimeRowsChain.cons
            · norm_num [dusartPrimeRow_of_explicit_16317]
            · norm_num [dusartPrimeRow_of_explicit_16317]
            · apply DusartPrimeRowsChain.cons
              · norm_num [dusartPrimeRow_of_explicit_16317]
              · norm_num [dusartPrimeRow_of_explicit_16317]
              · apply DusartPrimeRowsChain.cons
                · norm_num [dusartPrimeRow_of_explicit_16317]
                · norm_num [dusartPrimeRow_of_explicit_16317]
                · apply DusartPrimeRowsChain.empty
                  norm_num [dusartPrimeRow_of_explicit_16317, dusartPrimeRow_of_explicit_right]
