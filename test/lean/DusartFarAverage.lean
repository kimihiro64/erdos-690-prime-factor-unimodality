import PrimeFactorUnimodality.Helpers.Analytic.DusartFarAverage

/-! # Regression statements for the far-ray Dusart bounds -/

namespace PrimeFactorUnimodality.Tests

open Real

example (a δ : ℝ) {T U : ℝ} (hT : 10 ≤ T) (hTU : T ≤ U) :
    xiLowReciprocalNormBound a T δ ≤ xiLowReciprocalNormBound a U δ :=
  xiLowReciprocalNormBound_mono_height a δ hT hTU

example : xiLowReciprocalNormBound 10 200000000 (1 / 2) ≤ (70 : ℝ) :=
  xiLowReciprocalNormBound_half_le_of_le_billion (by norm_num) (by norm_num)

example {s x : ℝ}
    (hx : 1 < x) (hb : 4704 ≤ Real.log x)
    (hs₀ : exp (-(4 / 5 : ℝ) * sqrt (Real.log x / 6)) / 2 ≤ s)
    (hs₁ : s ≤ 2 * exp (-(4 / 5 : ℝ) * sqrt (Real.log x / 6))) :
    dusartBoxRosserRelativeBudget 0 s x 6 (4 / 5) 10 200000000 (1 / 2) ≤
      (1 / 100 : ℝ) / Real.log x ^ 2 :=
  dusartBoxRosserRelativeBudget_le_far_of_height_le hx hb hs₀ hs₁
    (by norm_num) (by norm_num)

example {b : ℝ} (hb : 4704 ≤ b) : 28 ≤ sqrt (b / 6) := by
  apply PrimeFactorUnimodality.dusartFar_root_ge <;> assumption

example {s x : ℝ}
    (hx : 1 < x) (hb : 4704 ≤ Real.log x)
    (hs₀ : exp (-(4 / 5 : ℝ) * sqrt (Real.log x / 6)) / 2 ≤ s)
    (hs₁ : s ≤ 2 * exp (-(4 / 5 : ℝ) * sqrt (Real.log x / 6))) :
    dusartBoxRosserRelativeBudget 0 s x 6 (4 / 5) 10 1000000000 (1 / 2) ≤
      (1 / 100 : ℝ) / Real.log x ^ 2 := by
  apply PrimeFactorUnimodality.dusartBoxRosserRelativeBudget_le_far <;> assumption

example {s x : ℝ}
    (hx : 1 < x) (hb : 4704 ≤ Real.log x)
    (hs₀ : exp (-(4 / 5 : ℝ) * sqrt (Real.log x / 6)) / 2 ≤ s)
    (hs₁ : s ≤ 2 * exp (-(4 / 5 : ℝ) * sqrt (Real.log x / 6)))
    (hgap : ∀ z ∈ xiLowHeightIndices 1000000000,
      (riemannXiDivisorZeroValue z).re ≤ (1 / 2 : ℝ))
    (hreg : ∀ z : RiemannXiDivisorZeroIndex, (1000000000 : ℝ) ≤
      |(riemannXiDivisorZeroValue z).im| → (riemannXiDivisorZeroValue z).re ≤
        1 - 1 / (6 * Real.log |(riemannXiDivisorZeroValue z).im|)) :
    |dusartPsiAverageError 3 (s * x) x| / x ≤ (1 / 100 : ℝ) / Real.log x ^ 2 := by
  apply PrimeFactorUnimodality.abs_dusartPsiAverageError_div_le_far <;> assumption

end PrimeFactorUnimodality.Tests
