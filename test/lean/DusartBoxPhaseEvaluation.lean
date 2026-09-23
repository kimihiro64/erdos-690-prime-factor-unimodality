import PrimeFactorUnimodality.Helpers.Analytic.DusartBoxPhaseEvaluation

/-! # Uniform frequency enclosures and real-window phase interpolation -/

open PrimeFactorUnimodality Complex Finset

example (m : ℕ) (s u T R v : ℝ) :
    dusartBoxLowPhaseSum m s u T (R * v) =
      ∑ z ∈ xiLowHeightIndices T, dusartBoxZeroCoefficient m s u z *
        exp (I * ((v * (R * (riemannXiDivisorZeroValue z).im) : ℝ) : ℂ)) :=
  dusartBoxLowPhaseSum_scaled m s u T R v

example (m : ℕ) (s u T : ℝ) (a : RiemannXiDivisorZeroIndex → ℂ)
    (g ε δ : RiemannXiDivisorZeroIndex → ℝ) {v V : ℝ} (hv : |v| ≤ V)
    (ha : ∀ z ∈ xiLowHeightIndices T, ‖dusartBoxZeroCoefficient m s u z - a z‖ ≤ ε z)
    (hg : ∀ z ∈ xiLowHeightIndices T, |(riemannXiDivisorZeroValue z).im - g z| ≤ δ z) :
    ‖dusartBoxLowPhaseSum m s u T v -
      ∑ z ∈ xiLowHeightIndices T, a z * exp (I * ((v * g z : ℝ) : ℂ))‖ ≤
      ∑ z ∈ xiLowHeightIndices T, (ε z + ‖a z‖ * (V * δ z)) :=
  norm_dusartBoxLowPhaseSum_sub_enclosures_le m s u T a g ε δ hv ha hg

example (m : ℕ) {s x T : ℝ} (u : ℝ)
    (hs : 0 < s) (hx : 1 < x) (hT : 10 < T)
    (hline : ∀ p ∈ xiLowHeightIndices T, (riemannXiDivisorZeroValue p).re = 1 / 2)
    {v d e : ℝ} {z : ℂ} (hd : |(Real.log x - u) - v| ≤ d)
    (hz : ‖dusartBoxLowPhaseSum m s u T v - z‖ ≤ e) :
    |dusartPsiAverageError (m + 3) (s * x) x| / x ≤
      dusartBoxPhaseBudget m s x T (‖z‖ + e + d * dusartBoxPhaseFrequencyMass m s u T) :=
  abs_dusartPsiAverageError_div_le_phase_sample m u hs hx hT hline hd hz

example (m : ℕ) (s u T v e : ℝ) {z : ℂ}
    (hz : ‖dusartBoxLowPhaseSum m s u T v - z‖ ≤ e) :
    ‖dusartBoxLowPhaseSum m s u T v‖ ≤ ‖z‖ + e := by
  simpa using norm_dusartBoxLowPhaseSum_le_of_sample m s u T
    (d := 0) (by simp : |v - v| ≤ 0) hz
