import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowBase

set_option autoImplicit false
set_option maxRecDepth 1000000

/-! # Lower finite Dusart prefix chunk 227 -/

namespace PrimeFactorUnimodality

noncomputable section
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_21577 : Nat.Prime 21577 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 21577 21576 1 5 [2, 2, 2, 3, 29, 31]
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
    · apply IsUnit.of_mul_eq_one (10788 : ZMod 21577)
      decide
    · apply IsUnit.of_mul_eq_one (12086 : ZMod 21577)
      decide
    · apply IsUnit.of_mul_eq_one (5426 : ZMod 21577)
      decide
    · apply IsUnit.of_mul_eq_one (10815 : ZMod 21577)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_21587 : Nat.Prime 21587 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 21587 21586 1 2 [2, 43, 251]
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
    · apply IsUnit.of_mul_eq_one (10793 : ZMod 21587)
      decide
    · apply IsUnit.of_mul_eq_one (14498 : ZMod 21587)
      decide
    · apply IsUnit.of_mul_eq_one (19534 : ZMod 21587)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_21589 : Nat.Prime 21589 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 21589 21588 1 2 [2, 2, 3, 7, 257]
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
    · apply IsUnit.of_mul_eq_one (10794 : ZMod 21589)
      decide
    · apply IsUnit.of_mul_eq_one (19378 : ZMod 21589)
      decide
    · apply IsUnit.of_mul_eq_one (9916 : ZMod 21589)
      decide
    · apply IsUnit.of_mul_eq_one (628 : ZMod 21589)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_21599 : Nat.Prime 21599 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 21599 21598 1 7 [2, 10799]
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
    · apply IsUnit.of_mul_eq_one (10799 : ZMod 21599)
      decide
    · apply IsUnit.of_mul_eq_one (450 : ZMod 21599)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_21601 : Nat.Prime 21601 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 21601 21600 1 7 [2, 2, 2, 2, 2, 3, 3, 3, 5, 5]
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
    · apply IsUnit.of_mul_eq_one (10800 : ZMod 21601)
      decide
    · apply IsUnit.of_mul_eq_one (13005 : ZMod 21601)
      decide
    · apply IsUnit.of_mul_eq_one (11701 : ZMod 21601)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_21611 : Nat.Prime 21611 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 21611 21610 1 2 [2, 5, 2161]
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
    · apply IsUnit.of_mul_eq_one (10805 : ZMod 21611)
      decide
    · apply IsUnit.of_mul_eq_one (15909 : ZMod 21611)
      decide
    · apply IsUnit.of_mul_eq_one (21442 : ZMod 21611)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_21613 : Nat.Prime 21613 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 21613 21612 1 2 [2, 2, 3, 1801]
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
    · apply IsUnit.of_mul_eq_one (10806 : ZMod 21613)
      decide
    · apply IsUnit.of_mul_eq_one (7974 : ZMod 21613)
      decide
    · apply IsUnit.of_mul_eq_one (19201 : ZMod 21613)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_21617 : Nat.Prime 21617 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 21617 21616 1 3 [2, 2, 2, 2, 7, 193]
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
    · apply IsUnit.of_mul_eq_one (10808 : ZMod 21617)
      decide
    · apply IsUnit.of_mul_eq_one (3158 : ZMod 21617)
      decide
    · apply IsUnit.of_mul_eq_one (13459 : ZMod 21617)
      decide
  · norm_num
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_20959_22026_part09 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_22026 (p := 21569) (q := 21577) (by exact lowPrime_21577) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_22026 (p := 21577) (q := 21587) (by exact lowPrime_21587) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_22026 (p := 21587) (q := 21589) (by exact lowPrime_21589) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_22026 (p := 21589) (q := 21599) (by exact lowPrime_21599) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_22026 (p := 21599) (q := 21601) (by exact lowPrime_21601) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_22026 (p := 21601) (q := 21611) (by exact lowPrime_21611) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_22026 (p := 21611) (q := 21613) (by exact lowPrime_21613) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_22026 (p := 21613) (q := 21617) (by exact lowPrime_21617) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_20959_22026_part09_chain :
    DusartPrimeRowsChain 21569 21616 dusartPrimeRows_20959_22026_part09 := by
  apply DusartPrimeRowsChain.cons
  · norm_num [dusartPrimeRow_of_explicit_22026]
  · norm_num [dusartPrimeRow_of_explicit_22026]
  · apply DusartPrimeRowsChain.cons
    · norm_num [dusartPrimeRow_of_explicit_22026]
    · norm_num [dusartPrimeRow_of_explicit_22026]
    · apply DusartPrimeRowsChain.cons
      · norm_num [dusartPrimeRow_of_explicit_22026]
      · norm_num [dusartPrimeRow_of_explicit_22026]
      · apply DusartPrimeRowsChain.cons
        · norm_num [dusartPrimeRow_of_explicit_22026]
        · norm_num [dusartPrimeRow_of_explicit_22026]
        · apply DusartPrimeRowsChain.cons
          · norm_num [dusartPrimeRow_of_explicit_22026]
          · norm_num [dusartPrimeRow_of_explicit_22026]
          · apply DusartPrimeRowsChain.cons
            · norm_num [dusartPrimeRow_of_explicit_22026]
            · norm_num [dusartPrimeRow_of_explicit_22026]
            · apply DusartPrimeRowsChain.cons
              · norm_num [dusartPrimeRow_of_explicit_22026]
              · norm_num [dusartPrimeRow_of_explicit_22026]
              · apply DusartPrimeRowsChain.cons
                · norm_num [dusartPrimeRow_of_explicit_22026]
                · norm_num [dusartPrimeRow_of_explicit_22026]
                · apply DusartPrimeRowsChain.empty
                  norm_num [dusartPrimeRow_of_explicit_22026, dusartPrimeRow_of_explicit_right]
