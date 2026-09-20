import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowBase

set_option autoImplicit false
set_option maxRecDepth 100000

/-! # Lower finite Dusart prefix chunk 187 -/

namespace PrimeFactorUnimodality

noncomputable section
set_option maxHeartbeats 20000000 in
theorem lowPrime_15901 : Nat.Prime 15901 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 15901 15900 1 10 [2, 2, 3, 5, 5, 53]
  · norm_num
  · norm_num
  · norm_num
  · intro p hp
    simp at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl
    all_goals decide
  · norm_num
  · norm_num
  · rw [← natCast_fastPowMod_eq_pow]
    decide
  · intro q hq
    simp at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · change IsUnit ((10 : ZMod 15901) ^ 7950 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (7950 : ZMod 15901)
      decide
    · change IsUnit ((10 : ZMod 15901) ^ 7950 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (7950 : ZMod 15901)
      decide
    · change IsUnit ((10 : ZMod 15901) ^ 5300 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (15206 : ZMod 15901)
      decide
    · change IsUnit ((10 : ZMod 15901) ^ 3180 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (10249 : ZMod 15901)
      decide
    · change IsUnit ((10 : ZMod 15901) ^ 3180 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (10249 : ZMod 15901)
      decide
    · change IsUnit ((10 : ZMod 15901) ^ 300 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (8540 : ZMod 15901)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_15907 : Nat.Prime 15907 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 15907 15906 1 2 [2, 3, 11, 241]
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
    · change IsUnit ((2 : ZMod 15907) ^ 7953 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (7953 : ZMod 15907)
      decide
    · change IsUnit ((2 : ZMod 15907) ^ 5302 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (6534 : ZMod 15907)
      decide
    · change IsUnit ((2 : ZMod 15907) ^ 1446 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (7818 : ZMod 15907)
      decide
    · change IsUnit ((2 : ZMod 15907) ^ 66 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (3401 : ZMod 15907)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_15913 : Nat.Prime 15913 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 15913 15912 1 5 [2, 2, 2, 3, 3, 13, 17]
  · norm_num
  · norm_num
  · norm_num
  · intro p hp
    simp at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals decide
  · norm_num
  · norm_num
  · rw [← natCast_fastPowMod_eq_pow]
    decide
  · intro q hq
    simp at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change IsUnit ((5 : ZMod 15913) ^ 7956 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (7956 : ZMod 15913)
      decide
    · change IsUnit ((5 : ZMod 15913) ^ 7956 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (7956 : ZMod 15913)
      decide
    · change IsUnit ((5 : ZMod 15913) ^ 7956 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (7956 : ZMod 15913)
      decide
    · change IsUnit ((5 : ZMod 15913) ^ 5304 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (4604 : ZMod 15913)
      decide
    · change IsUnit ((5 : ZMod 15913) ^ 5304 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (4604 : ZMod 15913)
      decide
    · change IsUnit ((5 : ZMod 15913) ^ 1224 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (5535 : ZMod 15913)
      decide
    · change IsUnit ((5 : ZMod 15913) ^ 936 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (3382 : ZMod 15913)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_15919 : Nat.Prime 15919 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 15919 15918 1 6 [2, 3, 7, 379]
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
    · change IsUnit ((6 : ZMod 15919) ^ 7959 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (7959 : ZMod 15919)
      decide
    · change IsUnit ((6 : ZMod 15919) ^ 5306 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (13445 : ZMod 15919)
      decide
    · change IsUnit ((6 : ZMod 15919) ^ 2274 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (61 : ZMod 15919)
      decide
    · change IsUnit ((6 : ZMod 15919) ^ 42 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (10184 : ZMod 15919)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_15923 : Nat.Prime 15923 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 15923 15922 1 2 [2, 19, 419]
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
    · change IsUnit ((2 : ZMod 15923) ^ 7961 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (7961 : ZMod 15923)
      decide
    · change IsUnit ((2 : ZMod 15923) ^ 838 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (4099 : ZMod 15923)
      decide
    · change IsUnit ((2 : ZMod 15923) ^ 38 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (3566 : ZMod 15923)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_15937 : Nat.Prime 15937 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 15937 15936 1 7 [2, 2, 2, 2, 2, 2, 3, 83]
  · norm_num
  · norm_num
  · norm_num
  · intro p hp
    simp at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals decide
  · norm_num
  · norm_num
  · rw [← natCast_fastPowMod_eq_pow]
    decide
  · intro q hq
    simp at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change IsUnit ((7 : ZMod 15937) ^ 7968 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (7968 : ZMod 15937)
      decide
    · change IsUnit ((7 : ZMod 15937) ^ 7968 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (7968 : ZMod 15937)
      decide
    · change IsUnit ((7 : ZMod 15937) ^ 7968 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (7968 : ZMod 15937)
      decide
    · change IsUnit ((7 : ZMod 15937) ^ 7968 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (7968 : ZMod 15937)
      decide
    · change IsUnit ((7 : ZMod 15937) ^ 7968 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (7968 : ZMod 15937)
      decide
    · change IsUnit ((7 : ZMod 15937) ^ 7968 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (7968 : ZMod 15937)
      decide
    · change IsUnit ((7 : ZMod 15937) ^ 5312 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (13336 : ZMod 15937)
      decide
    · change IsUnit ((7 : ZMod 15937) ^ 192 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (14811 : ZMod 15937)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_15959 : Nat.Prime 15959 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 15959 15958 1 11 [2, 79, 101]
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
    · change IsUnit ((11 : ZMod 15959) ^ 7979 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (7979 : ZMod 15959)
      decide
    · change IsUnit ((11 : ZMod 15959) ^ 202 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (15838 : ZMod 15959)
      decide
    · change IsUnit ((11 : ZMod 15959) ^ 158 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (15186 : ZMod 15959)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_15971 : Nat.Prime 15971 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 15971 15970 1 2 [2, 5, 1597]
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
    · change IsUnit ((2 : ZMod 15971) ^ 7985 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (7985 : ZMod 15971)
      decide
    · change IsUnit ((2 : ZMod 15971) ^ 3194 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (541 : ZMod 15971)
      decide
    · change IsUnit ((2 : ZMod 15971) ^ 10 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (1046 : ZMod 15971)
      decide
  · norm_num
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_15527_16318_part06 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_16317 (p := 15889) (q := 15901) (by exact lowPrime_15901) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_16317 (p := 15901) (q := 15907) (by exact lowPrime_15907) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_16317 (p := 15907) (q := 15913) (by exact lowPrime_15913) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_16317 (p := 15913) (q := 15919) (by exact lowPrime_15919) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_16317 (p := 15919) (q := 15923) (by exact lowPrime_15923) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_16317 (p := 15923) (q := 15937) (by exact lowPrime_15937) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_16317 (p := 15937) (q := 15959) (by exact lowPrime_15959) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_16317 (p := 15959) (q := 15971) (by exact lowPrime_15971) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_15527_16318_part06_chain :
    DusartPrimeRowsChain 15889 15971 dusartPrimeRows_15527_16318_part06 := by
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
                  norm_num
