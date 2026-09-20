import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowBase

set_option autoImplicit false
set_option maxRecDepth 1000000

/-! # Lower finite Dusart prefix chunk 183 -/

namespace PrimeFactorUnimodality

noncomputable section
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_15619 : Nat.Prime 15619 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 15619 15618 1 7 [2, 3, 19, 137]
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
    · apply IsUnit.of_mul_eq_one (7809 : ZMod 15619)
      decide
    · apply IsUnit.of_mul_eq_one (1448 : ZMod 15619)
      decide
    · apply IsUnit.of_mul_eq_one (10349 : ZMod 15619)
      decide
    · apply IsUnit.of_mul_eq_one (14566 : ZMod 15619)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_15629 : Nat.Prime 15629 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 15629 15628 1 2 [2, 2, 3907]
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
    · apply IsUnit.of_mul_eq_one (7814 : ZMod 15629)
      decide
    · apply IsUnit.of_mul_eq_one (1042 : ZMod 15629)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_15641 : Nat.Prime 15641 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 15641 15640 1 3 [2, 2, 2, 5, 17, 23]
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
    · apply IsUnit.of_mul_eq_one (7820 : ZMod 15641)
      decide
    · apply IsUnit.of_mul_eq_one (6903 : ZMod 15641)
      decide
    · apply IsUnit.of_mul_eq_one (13206 : ZMod 15641)
      decide
    · apply IsUnit.of_mul_eq_one (7100 : ZMod 15641)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_15643 : Nat.Prime 15643 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 15643 15642 1 5 [2, 3, 3, 11, 79]
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
    · apply IsUnit.of_mul_eq_one (7821 : ZMod 15643)
      decide
    · apply IsUnit.of_mul_eq_one (12069 : ZMod 15643)
      decide
    · apply IsUnit.of_mul_eq_one (1403 : ZMod 15643)
      decide
    · apply IsUnit.of_mul_eq_one (13825 : ZMod 15643)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_15647 : Nat.Prime 15647 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 15647 15646 1 5 [2, 7823]
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
    · apply IsUnit.of_mul_eq_one (7823 : ZMod 15647)
      decide
    · apply IsUnit.of_mul_eq_one (652 : ZMod 15647)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_15649 : Nat.Prime 15649 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 15649 15648 1 11 [2, 2, 2, 2, 2, 3, 163]
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
    · apply IsUnit.of_mul_eq_one (7824 : ZMod 15649)
      decide
    · apply IsUnit.of_mul_eq_one (8616 : ZMod 15649)
      decide
    · apply IsUnit.of_mul_eq_one (5213 : ZMod 15649)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_15661 : Nat.Prime 15661 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 15661 15660 1 2 [2, 2, 3, 3, 3, 5, 29]
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
    rcases hq with rfl | rfl | rfl | rfl
    · apply IsUnit.of_mul_eq_one (7830 : ZMod 15661)
      decide
    · apply IsUnit.of_mul_eq_one (13386 : ZMod 15661)
      decide
    · apply IsUnit.of_mul_eq_one (5363 : ZMod 15661)
      decide
    · apply IsUnit.of_mul_eq_one (3919 : ZMod 15661)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_15667 : Nat.Prime 15667 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 15667 15666 1 2 [2, 3, 7, 373]
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
    · apply IsUnit.of_mul_eq_one (7833 : ZMod 15667)
      decide
    · apply IsUnit.of_mul_eq_one (8259 : ZMod 15667)
      decide
    · apply IsUnit.of_mul_eq_one (13790 : ZMod 15667)
      decide
    · apply IsUnit.of_mul_eq_one (8447 : ZMod 15667)
      decide
  · norm_num
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_15527_16318_part02 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_16317 (p := 15607) (q := 15619) (by exact lowPrime_15619) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_16317 (p := 15619) (q := 15629) (by exact lowPrime_15629) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_16317 (p := 15629) (q := 15641) (by exact lowPrime_15641) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_16317 (p := 15641) (q := 15643) (by exact lowPrime_15643) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_16317 (p := 15643) (q := 15647) (by exact lowPrime_15647) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_16317 (p := 15647) (q := 15649) (by exact lowPrime_15649) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_16317 (p := 15649) (q := 15661) (by exact lowPrime_15661) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_16317 (p := 15661) (q := 15667) (by exact lowPrime_15667) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_15527_16318_part02_chain :
    DusartPrimeRowsChain 15607 15666 dusartPrimeRows_15527_16318_part02 := by
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
