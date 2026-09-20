import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowBase

set_option autoImplicit false
set_option maxRecDepth 1000000

/-! # Lower finite Dusart prefix chunk 252 -/

namespace PrimeFactorUnimodality

noncomputable section
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_19447 : Nat.Prime 19447 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 19447 19446 1 3 [2, 3, 7, 463]
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
    · apply IsUnit.of_mul_eq_one (9723 : ZMod 19447)
      decide
    · apply IsUnit.of_mul_eq_one (15541 : ZMod 19447)
      decide
    · apply IsUnit.of_mul_eq_one (17278 : ZMod 19447)
      decide
    · apply IsUnit.of_mul_eq_one (8375 : ZMod 19447)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_19457 : Nat.Prime 19457 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 19457 19456 1 3 [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 19]
  · norm_num
  · norm_num
  · norm_num
  · intro p hp
    simp at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals decide
  · norm_num
  · norm_num
  · decide
  · intro q hq
    simp at hq
    rcases hq with rfl | rfl
    · apply IsUnit.of_mul_eq_one (9728 : ZMod 19457)
      decide
    · apply IsUnit.of_mul_eq_one (13664 : ZMod 19457)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_19463 : Nat.Prime 19463 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 19463 19462 1 5 [2, 37, 263]
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
    · apply IsUnit.of_mul_eq_one (9731 : ZMod 19463)
      decide
    · apply IsUnit.of_mul_eq_one (4166 : ZMod 19463)
      decide
    · apply IsUnit.of_mul_eq_one (17962 : ZMod 19463)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_19469 : Nat.Prime 19469 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 19469 19468 1 2 [2, 2, 31, 157]
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
    · apply IsUnit.of_mul_eq_one (9734 : ZMod 19469)
      decide
    · apply IsUnit.of_mul_eq_one (2491 : ZMod 19469)
      decide
    · apply IsUnit.of_mul_eq_one (5531 : ZMod 19469)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_19471 : Nat.Prime 19471 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 19471 19470 1 11 [2, 3, 5, 11, 59]
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
    · apply IsUnit.of_mul_eq_one (9735 : ZMod 19471)
      decide
    · apply IsUnit.of_mul_eq_one (15923 : ZMod 19471)
      decide
    · apply IsUnit.of_mul_eq_one (7971 : ZMod 19471)
      decide
    · apply IsUnit.of_mul_eq_one (18792 : ZMod 19471)
      decide
    · apply IsUnit.of_mul_eq_one (6675 : ZMod 19471)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_19477 : Nat.Prime 19477 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 19477 19476 1 6 [2, 2, 3, 3, 541]
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
    · apply IsUnit.of_mul_eq_one (9738 : ZMod 19477)
      decide
    · apply IsUnit.of_mul_eq_one (14191 : ZMod 19477)
      decide
    · apply IsUnit.of_mul_eq_one (3042 : ZMod 19477)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_19483 : Nat.Prime 19483 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 19483 19482 1 2 [2, 3, 17, 191]
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
    · apply IsUnit.of_mul_eq_one (9741 : ZMod 19483)
      decide
    · apply IsUnit.of_mul_eq_one (1492 : ZMod 19483)
      decide
    · apply IsUnit.of_mul_eq_one (2681 : ZMod 19483)
      decide
    · apply IsUnit.of_mul_eq_one (2865 : ZMod 19483)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_19489 : Nat.Prime 19489 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 19489 19488 1 19 [2, 2, 2, 2, 2, 3, 7, 29]
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
    · apply IsUnit.of_mul_eq_one (9744 : ZMod 19489)
      decide
    · apply IsUnit.of_mul_eq_one (14332 : ZMod 19489)
      decide
    · apply IsUnit.of_mul_eq_one (4155 : ZMod 19489)
      decide
    · apply IsUnit.of_mul_eq_one (19205 : ZMod 19489)
      decide
  · norm_num
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_18959_19936_part07 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_19930 (p := 19441) (q := 19447) (by exact lowPrime_19447) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_19930 (p := 19447) (q := 19457) (by exact lowPrime_19457) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_19930 (p := 19457) (q := 19463) (by exact lowPrime_19463) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_19930 (p := 19463) (q := 19469) (by exact lowPrime_19469) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_19930 (p := 19469) (q := 19471) (by exact lowPrime_19471) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_19930 (p := 19471) (q := 19477) (by exact lowPrime_19477) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_19930 (p := 19477) (q := 19483) (by exact lowPrime_19483) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_19930 (p := 19483) (q := 19489) (by exact lowPrime_19489) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_18959_19936_part07_chain :
    DusartPrimeRowsChain 19441 19488 dusartPrimeRows_18959_19936_part07 := by
  apply DusartPrimeRowsChain.cons
  · norm_num [dusartPrimeRow_of_explicit_19930]
  · norm_num [dusartPrimeRow_of_explicit_19930]
  · apply DusartPrimeRowsChain.cons
    · norm_num [dusartPrimeRow_of_explicit_19930]
    · norm_num [dusartPrimeRow_of_explicit_19930]
    · apply DusartPrimeRowsChain.cons
      · norm_num [dusartPrimeRow_of_explicit_19930]
      · norm_num [dusartPrimeRow_of_explicit_19930]
      · apply DusartPrimeRowsChain.cons
        · norm_num [dusartPrimeRow_of_explicit_19930]
        · norm_num [dusartPrimeRow_of_explicit_19930]
        · apply DusartPrimeRowsChain.cons
          · norm_num [dusartPrimeRow_of_explicit_19930]
          · norm_num [dusartPrimeRow_of_explicit_19930]
          · apply DusartPrimeRowsChain.cons
            · norm_num [dusartPrimeRow_of_explicit_19930]
            · norm_num [dusartPrimeRow_of_explicit_19930]
            · apply DusartPrimeRowsChain.cons
              · norm_num [dusartPrimeRow_of_explicit_19930]
              · norm_num [dusartPrimeRow_of_explicit_19930]
              · apply DusartPrimeRowsChain.cons
                · norm_num [dusartPrimeRow_of_explicit_19930]
                · norm_num [dusartPrimeRow_of_explicit_19930]
                · apply DusartPrimeRowsChain.empty
                  norm_num [dusartPrimeRow_of_explicit_19930, dusartPrimeRow_of_explicit_right]
