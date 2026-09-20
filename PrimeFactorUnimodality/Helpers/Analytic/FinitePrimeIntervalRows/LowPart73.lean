import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowBase

set_option autoImplicit false
set_option maxRecDepth 100000

/-! # Lower finite Dusart prefix chunk 73 -/

namespace PrimeFactorUnimodality

noncomputable section
set_option maxHeartbeats 20000000 in
theorem lowPrime_7879 : Nat.Prime 7879 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 7879 7878 1 3 [2, 3, 13, 101]
  · norm_num
  · norm_num
  · norm_num
  · intro p hp
    simp at hp
    rcases hp with rfl | rfl | rfl | rfl
    all_goals decide
  · norm_num
  · norm_num
  · rw [← natCast_fastPowMod_eq_pow]
    decide
  · intro q hq
    simp at hq
    rcases hq with rfl | rfl | rfl | rfl
    · change IsUnit ((3 : ZMod 7879) ^ 3939 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (3939 : ZMod 7879)
      decide
    · change IsUnit ((3 : ZMod 7879) ^ 2626 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (7423 : ZMod 7879)
      decide
    · change IsUnit ((3 : ZMod 7879) ^ 606 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (1076 : ZMod 7879)
      decide
    · change IsUnit ((3 : ZMod 7879) ^ 78 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (4802 : ZMod 7879)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_7883 : Nat.Prime 7883 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 7883 7882 1 2 [2, 7, 563]
  · norm_num
  · norm_num
  · norm_num
  · intro p hp
    simp at hp
    rcases hp with rfl | rfl | rfl
    all_goals decide
  · norm_num
  · norm_num
  · rw [← natCast_fastPowMod_eq_pow]
    decide
  · intro q hq
    simp at hq
    rcases hq with rfl | rfl | rfl
    · change IsUnit ((2 : ZMod 7883) ^ 3941 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (3941 : ZMod 7883)
      decide
    · change IsUnit ((2 : ZMod 7883) ^ 1126 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (7597 : ZMod 7883)
      decide
    · change IsUnit ((2 : ZMod 7883) ^ 14 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (6912 : ZMod 7883)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_7901 : Nat.Prime 7901 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 7901 7900 1 2 [2, 2, 5, 5, 79]
  · norm_num
  · norm_num
  · norm_num
  · intro p hp
    simp at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl
    all_goals decide
  · norm_num
  · norm_num
  · rw [← natCast_fastPowMod_eq_pow]
    decide
  · intro q hq
    simp at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · change IsUnit ((2 : ZMod 7901) ^ 3950 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (3950 : ZMod 7901)
      decide
    · change IsUnit ((2 : ZMod 7901) ^ 3950 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (3950 : ZMod 7901)
      decide
    · change IsUnit ((2 : ZMod 7901) ^ 1580 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (4943 : ZMod 7901)
      decide
    · change IsUnit ((2 : ZMod 7901) ^ 1580 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (4943 : ZMod 7901)
      decide
    · change IsUnit ((2 : ZMod 7901) ^ 100 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (92 : ZMod 7901)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_7907 : Nat.Prime 7907 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 7907 7906 1 2 [2, 59, 67]
  · norm_num
  · norm_num
  · norm_num
  · intro p hp
    simp at hp
    rcases hp with rfl | rfl | rfl
    all_goals decide
  · norm_num
  · norm_num
  · rw [← natCast_fastPowMod_eq_pow]
    decide
  · intro q hq
    simp at hq
    rcases hq with rfl | rfl | rfl
    · change IsUnit ((2 : ZMod 7907) ^ 3953 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (3953 : ZMod 7907)
      decide
    · change IsUnit ((2 : ZMod 7907) ^ 134 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (3922 : ZMod 7907)
      decide
    · change IsUnit ((2 : ZMod 7907) ^ 118 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (813 : ZMod 7907)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_7919 : Nat.Prime 7919 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 7919 7918 1 7 [2, 37, 107]
  · norm_num
  · norm_num
  · norm_num
  · intro p hp
    simp at hp
    rcases hp with rfl | rfl | rfl
    all_goals decide
  · norm_num
  · norm_num
  · rw [← natCast_fastPowMod_eq_pow]
    decide
  · intro q hq
    simp at hq
    rcases hq with rfl | rfl | rfl
    · change IsUnit ((7 : ZMod 7919) ^ 3959 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (3959 : ZMod 7919)
      decide
    · change IsUnit ((7 : ZMod 7919) ^ 214 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (5934 : ZMod 7919)
      decide
    · change IsUnit ((7 : ZMod 7919) ^ 74 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (3370 : ZMod 7919)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_7927 : Nat.Prime 7927 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 7927 7926 1 3 [2, 3, 1321]
  · norm_num
  · norm_num
  · norm_num
  · intro p hp
    simp at hp
    rcases hp with rfl | rfl | rfl
    all_goals decide
  · norm_num
  · norm_num
  · rw [← natCast_fastPowMod_eq_pow]
    decide
  · intro q hq
    simp at hq
    rcases hq with rfl | rfl | rfl
    · change IsUnit ((3 : ZMod 7927) ^ 3963 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (3963 : ZMod 7927)
      decide
    · change IsUnit ((3 : ZMod 7927) ^ 2642 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (3895 : ZMod 7927)
      decide
    · change IsUnit ((3 : ZMod 7927) ^ 6 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (98 : ZMod 7927)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_7933 : Nat.Prime 7933 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 7933 7932 1 2 [2, 2, 3, 661]
  · norm_num
  · norm_num
  · norm_num
  · intro p hp
    simp at hp
    rcases hp with rfl | rfl | rfl | rfl
    all_goals decide
  · norm_num
  · norm_num
  · rw [← natCast_fastPowMod_eq_pow]
    decide
  · intro q hq
    simp at hq
    rcases hq with rfl | rfl | rfl | rfl
    · change IsUnit ((2 : ZMod 7933) ^ 3966 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (3966 : ZMod 7933)
      decide
    · change IsUnit ((2 : ZMod 7933) ^ 3966 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (3966 : ZMod 7933)
      decide
    · change IsUnit ((2 : ZMod 7933) ^ 2644 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (668 : ZMod 7933)
      decide
    · change IsUnit ((2 : ZMod 7933) ^ 12 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (3735 : ZMod 7933)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_7937 : Nat.Prime 7937 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 7937 7936 1 3 [2, 2, 2, 2, 2, 2, 2, 2, 31]
  · norm_num
  · norm_num
  · norm_num
  · intro p hp
    simp at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals decide
  · norm_num
  · norm_num
  · rw [← natCast_fastPowMod_eq_pow]
    decide
  · intro q hq
    simp at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change IsUnit ((3 : ZMod 7937) ^ 3968 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (3968 : ZMod 7937)
      decide
    · change IsUnit ((3 : ZMod 7937) ^ 3968 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (3968 : ZMod 7937)
      decide
    · change IsUnit ((3 : ZMod 7937) ^ 3968 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (3968 : ZMod 7937)
      decide
    · change IsUnit ((3 : ZMod 7937) ^ 3968 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (3968 : ZMod 7937)
      decide
    · change IsUnit ((3 : ZMod 7937) ^ 3968 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (3968 : ZMod 7937)
      decide
    · change IsUnit ((3 : ZMod 7937) ^ 3968 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (3968 : ZMod 7937)
      decide
    · change IsUnit ((3 : ZMod 7937) ^ 3968 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (3968 : ZMod 7937)
      decide
    · change IsUnit ((3 : ZMod 7937) ^ 3968 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (3968 : ZMod 7937)
      decide
    · change IsUnit ((3 : ZMod 7937) ^ 256 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (4154 : ZMod 7937)
      decide
  · norm_num
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_7717_8110_part03 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_8103 (p := 7877) (q := 7879) (by exact lowPrime_7879) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8103 (p := 7879) (q := 7883) (by exact lowPrime_7883) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8103 (p := 7883) (q := 7901) (by exact lowPrime_7901) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8103 (p := 7901) (q := 7907) (by exact lowPrime_7907) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8103 (p := 7907) (q := 7919) (by exact lowPrime_7919) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8103 (p := 7919) (q := 7927) (by exact lowPrime_7927) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8103 (p := 7927) (q := 7933) (by exact lowPrime_7933) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8103 (p := 7933) (q := 7937) (by exact lowPrime_7937) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_7717_8110_part03_chain :
    DusartPrimeRowsChain 7877 7937 dusartPrimeRows_7717_8110_part03 := by
  apply DusartPrimeRowsChain.cons
  · norm_num [dusartPrimeRow_of_explicit_8103]
  · norm_num [dusartPrimeRow_of_explicit_8103]
  · apply DusartPrimeRowsChain.cons
    · norm_num [dusartPrimeRow_of_explicit_8103]
    · norm_num [dusartPrimeRow_of_explicit_8103]
    · apply DusartPrimeRowsChain.cons
      · norm_num [dusartPrimeRow_of_explicit_8103]
      · norm_num [dusartPrimeRow_of_explicit_8103]
      · apply DusartPrimeRowsChain.cons
        · norm_num [dusartPrimeRow_of_explicit_8103]
        · norm_num [dusartPrimeRow_of_explicit_8103]
        · apply DusartPrimeRowsChain.cons
          · norm_num [dusartPrimeRow_of_explicit_8103]
          · norm_num [dusartPrimeRow_of_explicit_8103]
          · apply DusartPrimeRowsChain.cons
            · norm_num [dusartPrimeRow_of_explicit_8103]
            · norm_num [dusartPrimeRow_of_explicit_8103]
            · apply DusartPrimeRowsChain.cons
              · norm_num [dusartPrimeRow_of_explicit_8103]
              · norm_num [dusartPrimeRow_of_explicit_8103]
              · apply DusartPrimeRowsChain.cons
                · norm_num [dusartPrimeRow_of_explicit_8103]
                · norm_num [dusartPrimeRow_of_explicit_8103]
                · apply DusartPrimeRowsChain.empty
                  norm_num
