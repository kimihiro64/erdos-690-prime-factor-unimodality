import PrimeFactorUnimodality.Helpers.Analytic.DusartEarlierCutoffBudget

/-! # Earlier analytic cutoff interfaces and seam regressions -/

set_option autoImplicit false

namespace PrimeFactorUnimodality.Tests

noncomputable section

open Real

example {s : ℝ} (hs : s ≤ (1 / 49997 : ℝ)) :
    1 + 3 * s ≤ (10001 / 10000 : ℝ) := by
  exact PrimeFactorUnimodality.dusartEarlier_width_le hs

example {s : ℝ} (hs₀ : (1 / 50000 : ℝ) ≤ s)
    (hs₁ : s ≤ (1 / 49997 : ℝ)) :
    8 * (1 + 3 * s) ^ 4 / s ^ 3 ≤ (1001 * 10 ^ 12 : ℝ) := by
  exact PrimeFactorUnimodality.dusartEarlier_high_coefficient_le hs₀ hs₁

example {s x r : ℝ}
    (hs₀ : (1 / 50000 : ℝ) ≤ s) (hs₁ : s ≤ (1 / 49997 : ℝ))
    (hr : 2 ≤ r) (hx : r ^ 2 ≤ x) :
    dusartBoxPowerRelativeBudget 0 s x 25 100000 25000000 (1 / 2) ≤
      dusartEarlierAverageCap r := by
  exact PrimeFactorUnimodality.dusartBoxPowerRelativeBudget_earlier_le hs₀ hs₁ hr hx

example {x₀ r : ℝ} (hr : 2 ≤ r)
    (hx₀ : r ^ 2 ≤ x₀ * (1 - 3 * (1 / 50000))) :
    dusartBoxPowerPsiBound 0 (1 / 50000) x₀ 25 100000 25000000 (1 / 2) ≤
      dusartEarlierAverageCap r + 3 / 100000 := by
  exact PrimeFactorUnimodality.dusartBoxPowerPsiBound_earlier_le hr hx₀

example {x₀ x r : ℝ} (hr : 2 ≤ r)
    (hx₀ : r ^ 2 ≤ x₀ * (1 - 3 * (1 / 50000))) (hx : x₀ ≤ x)
    (hgap : ∀ z ∈ xiLowHeightIndices 25000000,
      (riemannXiDivisorZeroValue z).re ≤ (1 / 2 : ℝ)) :
    |Chebyshev.psi x - x| / x ≤ dusartEarlierAverageCap r + 3 / 100000 := by
  exact PrimeFactorUnimodality.abs_psi_sub_div_le_earlier hr hx₀ hx hgap

example : dusartBoxPowerPsiBound 0 (1 / 50000) 10000000000 25 100000 25000000 (1 / 2) ≤
    dusartEarlierAverageCap 99000 + 3 / 100000 :=
  dusartBoxPowerPsiBound_earlier_le (by norm_num) (by norm_num)

example : dusartBoxPowerPsiBound 0 (1 / 50000) 100000000000 25 100000 25000000 (1 / 2) ≤
    dusartEarlierAverageCap 300000 + 3 / 100000 :=
  dusartBoxPowerPsiBound_earlier_le (by norm_num) (by norm_num)

example : (dusartEarlierAverageCap 99000 + 3 / 100000 + 6 / 100000) * 26 ^ 2 ≤
    (1 / 5 : ℝ) := by norm_num [dusartEarlierAverageCap]

example : (dusartEarlierAverageCap 300000 + 3 / 100000 + 6 / 300000) * 30 ^ 2 ≤
    (1 / 5 : ℝ) := by norm_num [dusartEarlierAverageCap]

end

end PrimeFactorUnimodality.Tests
