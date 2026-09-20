import PrimeFactorUnimodality.Helpers.Analytic.DusartIntermediateCoeffData
import PrimeFactorUnimodality.Helpers.Analytic.DusartPowerSumAssembly

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

/-! # Dusart intermediate power sum

This module assembles the reusable coefficient table into the required
power-sum estimate. -/

namespace PrimeFactorUnimodality

noncomputable section

/- The reusable coefficient table controls every exponent from 4 through the
   first thirty intermediate powers; all larger exponents use its last row. -/
theorem dusart_intermediate_power_sum_bound
    {x : Real} (hx : 1 ≤ x) {N : Nat}
    (hN : 23 ≤ N) (hN' : N ≤ 109)
    (hbase : (2 ^ N : Real) ≤ x) :
    ∑ k ∈ Finset.Icc 3 N, x ^ (1 / (k : Real)) ≤
      (1 +
        (∑ k ∈ Finset.Icc 4 (min N 30),
          (dusartIntermediateCoeff N k : Real) / 10000) +
        ((N - min N 30 : Nat) : Real) *
          ((dusartIntermediateCoeff N (min N 30 + 1) : Real) / 10000)) *
        x ^ (1 / (3 : Real)) := by
  let K : Nat := min N 30
  let q : Nat → Real := fun k =>
    (dusartIntermediateCoeff N k : Real) / 10000
  have hK : 4 ≤ K := by
    dsimp [K]
    exact Nat.le_min (by omega) (by omega)
  have hKN : K ≤ N := by
    exact Nat.min_le_left _ _
  have hKlow : 23 ≤ K := by
    dsimp [K]
    exact Nat.le_min hN (by omega)
  have hKplus : 4 ≤ K + 1 ∧ K + 1 ≤ 31 := by
    omega
  have hfinite : ∀ k ∈ Finset.Icc 4 K,
      x ^ (1 / (k : Real)) ≤ q k * x ^ (1 / (3 : Real)) := by
    intro k hk
    have hkmem := Finset.mem_Icc.mp hk
    have hpow := dusartIntermediateCoeff_power hN hN' hkmem.1
      (by omega : k ≤ 31)
    have hratio := dusart_rpow_ratio_bound
      (x := x) (b := (2 ^ N : Real)) (q := q k) (k := k)
      (by positivity) hbase hkmem.1
      (by positivity) (by simpa [q] using hpow)
    exact hratio
  have htailbase :
      x ^ (1 / ((K + 1 : Nat) : Real)) ≤
        q (K + 1) * x ^ (1 / (3 : Real)) := by
    have hpow := dusartIntermediateCoeff_power hN hN'
      hKplus.1 hKplus.2
    exact dusart_rpow_ratio_bound
      (x := x) (b := (2 ^ N : Real)) (q := q (K + 1))
      (by positivity) hbase (by omega) (by positivity)
      (by simpa [q] using hpow)
  have htail : ∀ k ∈ Finset.Icc (K + 1) N,
      x ^ (1 / (k : Real)) ≤ q (K + 1) * x ^ (1 / (3 : Real)) := by
    intro k hk
    have hkmem := Finset.mem_Icc.mp hk
    calc
      x ^ (1 / (k : Real)) ≤
          x ^ (1 / ((K + 1 : Nat) : Real)) := by
        apply Real.rpow_le_rpow_of_exponent_le hx
        apply one_div_le_one_div_of_le
        · norm_num
        · exact_mod_cast hkmem.1
      _ ≤ q (K + 1) * x ^ (1 / (3 : Real)) := htailbase
  have hsum := dusart_power_sum_of_finite_and_tail hx q hK hKN
    hfinite htail
  simpa [K, q] using hsum


theorem dusart_intermediate_power_sum_bound_relaxed
    {x : Real} (hx : 1 ≤ x) {N : Nat}
    (hN : 23 ≤ N) (hN' : N ≤ 109)
    (hbase : (2 ^ N : Real) ≤ x) :
    ∑ k ∈ Finset.Icc 3 N, x ^ (1 / (k : Real)) ≤
      (1777 : Real) / 1000 * x ^ (1 / (3 : Real)) := by
  have hsum := dusart_intermediate_power_sum_bound hx hN hN' hbase
  have hmargin := dusartIntermediateCoeff_margin hN hN'
  calc
    ∑ k ∈ Finset.Icc 3 N, x ^ (1 / (k : Real)) ≤
        (1 +
          (∑ k ∈ Finset.Icc 4 (min N 30),
            (dusartIntermediateCoeff N k : Real) / 10000) +
          ((N - min N 30 : Nat) : Real) *
            ((dusartIntermediateCoeff N (min N 30 + 1) : Real) / 10000)) *
          x ^ (1 / (3 : Real)) := hsum
    _ ≤ (1777 : Real) / 1000 * x ^ (1 / (3 : Real)) := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      nlinarith
end

end PrimeFactorUnimodality
