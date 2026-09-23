import PrimeFactorUnimodality.Helpers.Analytic.DusartBoxOscillation

/-! # Exact low-zero identity at arbitrary logarithmic centers -/

open PrimeFactorUnimodality Complex intervalIntegral

example (m : ℕ) {s x T : ℝ} (u : ℝ) (hs : 0 < s) (hx : 0 < x)
    (hline : ∀ z ∈ xiLowHeightIndices T, (riemannXiDivisorZeroValue z).re = 1 / 2) :
    (∑ z ∈ xiLowHeightIndices T, iteratedBoxAverageComplex (s * x) (m + 3)
      (fun t => (t : ℂ) ^ riemannXiDivisorZeroValue z / riemannXiDivisorZeroValue z) x) =
      (Real.exp (Real.log x / 2) : ℂ) * dusartBoxLowPhaseSum m s u T (Real.log x - u) :=
  dusartBox_low_eq_phase m u hs hx hline

example (m : ℕ) {s x T : ℝ} (hs : 0 < s) (hx : 0 < x)
    (hline : ∀ z ∈ xiLowHeightIndices T, (riemannXiDivisorZeroValue z).re = 1 / 2) :
    ‖∑ z ∈ xiLowHeightIndices T, iteratedBoxAverageComplex (s * x) (m + 3)
      (fun t => (t : ℂ) ^ riemannXiDivisorZeroValue z / riemannXiDivisorZeroValue z) x‖ / x =
      Real.exp (-Real.log x / 2) * ‖dusartBoxLowPhaseSum m s (Real.log x) T 0‖ := by
  simpa using norm_dusartBox_low_div_eq_phase m (Real.log x) hs hx hline
