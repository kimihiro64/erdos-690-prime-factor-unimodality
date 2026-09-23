import PrimeFactorUnimodality.Helpers.Analytic.DusartBoxCoefficientStability

/-! # Uniform ordinate sensitivity includes centering and arbitrary smoothing order -/

open PrimeFactorUnimodality

example (m : ℕ) {s L γ δ : ℝ} (hs : 0 < s) (u : ℝ) (hL : 0 < L)
    (hγ : L ≤ γ) (hδ : L ≤ δ) :
    ‖dusartBoxOrdinateCoefficient m s u γ - dusartBoxOrdinateCoefficient m s u δ‖ ≤
      dusartBoxCoefficientSlope m s u L * |γ - δ| :=
  norm_dusartBoxOrdinateCoefficient_sub_le m hs u hL hγ hδ

example (m : ℕ) {s L γ : ℝ} (hs : 0 < s) (u : ℝ) (hL : 0 < L) (hγ : L ≤ γ) :
    ‖dusartBoxOrdinateCoefficient m s u γ‖ ≤ dusartBoxCoefficientAmplitude m s / L :=
  norm_dusartBoxOrdinateCoefficient_le m hs u hL hγ

example (m : ℕ) {s L γ δ r e : ℝ} (hs : 0 < s) (u : ℝ) (hL : 0 < L)
    (hγ : L ≤ γ) (hδ : L ≤ δ) (hr : |γ - δ| ≤ r) {c : ℂ}
    (hc : ‖dusartBoxOrdinateCoefficient m s u δ - c‖ ≤ e) :
    ‖dusartBoxOrdinateCoefficient m s u γ - c‖ ≤ dusartBoxCoefficientSlope m s u L * r + e :=
  norm_dusartBoxOrdinateCoefficient_sub_center_le m hs u hL hγ hδ hr hc
