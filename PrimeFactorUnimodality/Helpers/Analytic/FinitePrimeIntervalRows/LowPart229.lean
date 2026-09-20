import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowBase

set_option autoImplicit false
set_option maxRecDepth 1000000

/-! # Lower finite Dusart prefix chunk 229 -/

namespace PrimeFactorUnimodality

noncomputable section
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_21737 : Nat.Prime 21737 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 21737 21736 1 6 [2, 2, 2, 11, 13, 19]
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
    · apply IsUnit.of_mul_eq_one (10868 : ZMod 21737)
      decide
    · apply IsUnit.of_mul_eq_one (7760 : ZMod 21737)
      decide
    · apply IsUnit.of_mul_eq_one (13561 : ZMod 21737)
      decide
    · apply IsUnit.of_mul_eq_one (5733 : ZMod 21737)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_21739 : Nat.Prime 21739 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 21739 21738 1 2 [2, 3, 3623]
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
    · apply IsUnit.of_mul_eq_one (10869 : ZMod 21739)
      decide
    · apply IsUnit.of_mul_eq_one (12233 : ZMod 21739)
      decide
    · apply IsUnit.of_mul_eq_one (16218 : ZMod 21739)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_21751 : Nat.Prime 21751 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 21751 21750 1 3 [2, 3, 5, 5, 5, 29]
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
    · apply IsUnit.of_mul_eq_one (10875 : ZMod 21751)
      decide
    · apply IsUnit.of_mul_eq_one (19070 : ZMod 21751)
      decide
    · apply IsUnit.of_mul_eq_one (18854 : ZMod 21751)
      decide
    · apply IsUnit.of_mul_eq_one (20340 : ZMod 21751)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_21757 : Nat.Prime 21757 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 21757 21756 1 5 [2, 2, 3, 7, 7, 37]
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
    · apply IsUnit.of_mul_eq_one (10878 : ZMod 21757)
      decide
    · apply IsUnit.of_mul_eq_one (14455 : ZMod 21757)
      decide
    · apply IsUnit.of_mul_eq_one (11136 : ZMod 21757)
      decide
    · apply IsUnit.of_mul_eq_one (10797 : ZMod 21757)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_21767 : Nat.Prime 21767 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 21767 21766 1 5 [2, 10883]
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
    · apply IsUnit.of_mul_eq_one (10883 : ZMod 21767)
      decide
    · apply IsUnit.of_mul_eq_one (907 : ZMod 21767)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_21773 : Nat.Prime 21773 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 21773 21772 1 2 [2, 2, 5443]
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
    · apply IsUnit.of_mul_eq_one (10886 : ZMod 21773)
      decide
    · apply IsUnit.of_mul_eq_one (18870 : ZMod 21773)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_21787 : Nat.Prime 21787 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 21787 21786 1 23 [2, 3, 3631]
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
    · apply IsUnit.of_mul_eq_one (10893 : ZMod 21787)
      decide
    · apply IsUnit.of_mul_eq_one (20308 : ZMod 21787)
      decide
    · apply IsUnit.of_mul_eq_one (823 : ZMod 21787)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_21799 : Nat.Prime 21799 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 21799 21798 1 7 [2, 3, 3, 7, 173]
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
    · apply IsUnit.of_mul_eq_one (10899 : ZMod 21799)
      decide
    · apply IsUnit.of_mul_eq_one (1659 : ZMod 21799)
      decide
    · apply IsUnit.of_mul_eq_one (12191 : ZMod 21799)
      decide
    · apply IsUnit.of_mul_eq_one (15652 : ZMod 21799)
      decide
  · norm_num
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_20959_22026_part11 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_22026 (p := 21727) (q := 21737) (by exact lowPrime_21737) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_22026 (p := 21737) (q := 21739) (by exact lowPrime_21739) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_22026 (p := 21739) (q := 21751) (by exact lowPrime_21751) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_22026 (p := 21751) (q := 21757) (by exact lowPrime_21757) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_22026 (p := 21757) (q := 21767) (by exact lowPrime_21767) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_22026 (p := 21767) (q := 21773) (by exact lowPrime_21773) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_22026 (p := 21773) (q := 21787) (by exact lowPrime_21787) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_22026 (p := 21787) (q := 21799) (by exact lowPrime_21799) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_20959_22026_part11_chain :
    DusartPrimeRowsChain 21727 21798 dusartPrimeRows_20959_22026_part11 := by
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
