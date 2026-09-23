import PrimeFactorUnimodality.Helpers.Analytic.DusartBoxCoefficientSamples

/-! # Finite power samples, exact denominator and separate rounding errors -/

open PrimeFactorUnimodality Complex Finset

example (m : ℕ) {s : ℝ} (hs : 0 < s) (u γ : ℝ) :
    dusartBoxOrdinateCoefficient m s u γ =
      dusartBoxCoefficientNumerator m
        (fun j => ((1 + j • s : ℝ) : ℂ) ^ ((1 / 2 : ℂ) + γ * I + (m + 3 : ℕ))) /
          dusartBoxCoefficientDenom m s γ * exp (I * ↑(u * γ)) :=
  dusartBoxOrdinateCoefficient_eq_samples m hs u γ

example (m : ℕ) {s : ℝ} (hs : 0 < s) : dusartBoxCoefficientDenom m s 0 ≠ 0 :=
  dusartBoxCoefficientDenom_ne_zero m hs 0

example (m : ℕ) {s : ℝ} (hs : 0 < s) (u γ : ℝ) (v : ℕ → ℂ) (e : ℕ → ℝ)
    (he : ∀ j ∈ range (m + 4),
      ‖((1 + j • s : ℝ) : ℂ) ^ ((1 / 2 : ℂ) + γ * I + (m + 3 : ℕ)) - v j‖ ≤ e j)
    {p c : ℂ} {η r : ℝ} (hp : ‖exp (I * ↑(u * γ)) - p‖ ≤ η)
    (hc : ‖dusartBoxCoefficientNumerator m v / dusartBoxCoefficientDenom m s γ * p - c‖ ≤ r) :
    ‖dusartBoxOrdinateCoefficient m s u γ - c‖ ≤
      (∑ j ∈ range (m + 4), ((m + 3).choose j : ℝ) * e j) /
          ‖dusartBoxCoefficientDenom m s γ‖ +
        ‖dusartBoxCoefficientNumerator m v / dusartBoxCoefficientDenom m s γ‖ * η + r :=
  norm_dusartBoxOrdinateCoefficient_sub_checked_samples_le m hs u γ v e he hp hc
