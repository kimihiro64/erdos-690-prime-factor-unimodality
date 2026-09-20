import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowBase

set_option autoImplicit false
set_option maxRecDepth 1000000

/-! # Lower finite Dusart prefix chunk 188 -/

namespace PrimeFactorUnimodality

noncomputable section
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_15973 : Nat.Prime 15973 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 15973 15972 1 7 [2, 2, 3, 11, 11, 11]
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
    · apply IsUnit.of_mul_eq_one (7986 : ZMod 15973)
      decide
    · apply IsUnit.of_mul_eq_one (4979 : ZMod 15973)
      decide
    · apply IsUnit.of_mul_eq_one (621 : ZMod 15973)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_15991 : Nat.Prime 15991 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 15991 15990 1 12 [2, 3, 5, 13, 41]
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
    · apply IsUnit.of_mul_eq_one (7995 : ZMod 15991)
      decide
    · apply IsUnit.of_mul_eq_one (12011 : ZMod 15991)
      decide
    · apply IsUnit.of_mul_eq_one (4639 : ZMod 15991)
      decide
    · apply IsUnit.of_mul_eq_one (7159 : ZMod 15991)
      decide
    · apply IsUnit.of_mul_eq_one (11434 : ZMod 15991)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_16001 : Nat.Prime 16001 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 16001 16000 1 3 [2, 2, 2, 2, 2, 2, 2, 5, 5, 5]
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
    rcases hq with rfl | rfl
    · apply IsUnit.of_mul_eq_one (8000 : ZMod 16001)
      decide
    · apply IsUnit.of_mul_eq_one (9893 : ZMod 16001)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_16007 : Nat.Prime 16007 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 16007 16006 1 5 [2, 53, 151]
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
    · apply IsUnit.of_mul_eq_one (8003 : ZMod 16007)
      decide
    · apply IsUnit.of_mul_eq_one (8953 : ZMod 16007)
      decide
    · apply IsUnit.of_mul_eq_one (13550 : ZMod 16007)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_16033 : Nat.Prime 16033 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 16033 16032 1 5 [2, 2, 2, 2, 2, 3, 167]
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
    · apply IsUnit.of_mul_eq_one (8016 : ZMod 16033)
      decide
    · apply IsUnit.of_mul_eq_one (7656 : ZMod 16033)
      decide
    · apply IsUnit.of_mul_eq_one (9045 : ZMod 16033)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_16057 : Nat.Prime 16057 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 16057 16056 1 7 [2, 2, 2, 3, 3, 223]
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
    · apply IsUnit.of_mul_eq_one (8028 : ZMod 16057)
      decide
    · apply IsUnit.of_mul_eq_one (3789 : ZMod 16057)
      decide
    · apply IsUnit.of_mul_eq_one (7414 : ZMod 16057)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_16061 : Nat.Prime 16061 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 16061 16060 1 12 [2, 2, 5, 11, 73]
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
    · apply IsUnit.of_mul_eq_one (8030 : ZMod 16061)
      decide
    · apply IsUnit.of_mul_eq_one (7846 : ZMod 16061)
      decide
    · apply IsUnit.of_mul_eq_one (13647 : ZMod 16061)
      decide
    · apply IsUnit.of_mul_eq_one (10402 : ZMod 16061)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_16063 : Nat.Prime 16063 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 16063 16062 1 5 [2, 3, 2677]
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
    · apply IsUnit.of_mul_eq_one (8031 : ZMod 16063)
      decide
    · apply IsUnit.of_mul_eq_one (9523 : ZMod 16063)
      decide
    · apply IsUnit.of_mul_eq_one (12404 : ZMod 16063)
      decide
  · norm_num
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_15527_16318_part07 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_16317 (p := 15971) (q := 15973) (by exact lowPrime_15973) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_16317 (p := 15973) (q := 15991) (by exact lowPrime_15991) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_16317 (p := 15991) (q := 16001) (by exact lowPrime_16001) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_16317 (p := 16001) (q := 16007) (by exact lowPrime_16007) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_16317 (p := 16007) (q := 16033) (by exact lowPrime_16033) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_16317 (p := 16033) (q := 16057) (by exact lowPrime_16057) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_16317 (p := 16057) (q := 16061) (by exact lowPrime_16061) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_16317 (p := 16061) (q := 16063) (by exact lowPrime_16063) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_15527_16318_part07_chain :
    DusartPrimeRowsChain 15971 16062 dusartPrimeRows_15527_16318_part07 := by
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
