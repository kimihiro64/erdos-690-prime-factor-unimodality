import PrimeFactorUnimodality.Helpers.Analytic.DusartBoxPhaseBudget

/-! # Full correction and adjacent-average phase consumers -/

open PrimeFactorUnimodality

example (m : ℕ) {s x T B : ℝ} (u : ℝ) (hs : 0 < s) (hx : 1 < x) (hT : 10 < T)
    (hline : ∀ z ∈ xiLowHeightIndices T, (riemannXiDivisorZeroValue z).re = 1 / 2)
    (hphase : ‖dusartBoxLowPhaseSum m s u T (Real.log x - u)‖ ≤ B) :
    |dusartPsiAverageError (m + 3) (s * x) x| / x ≤ dusartBoxPhaseBudget m s x T B :=
  abs_dusartPsiAverageError_div_le_phase m u hs hx hT hline hphase

example (m : ℕ) {s x T L U : ℝ} (u v : ℝ)
    (hs : 0 < s) (hx : 1 < x) (hT : 10 < T)
    (hq : 0 < 1 - (m + 3 : ℕ) * s) (hy : 1 < x * (1 - (m + 3 : ℕ) * s))
    (hline : ∀ z ∈ xiLowHeightIndices T, (riemannXiDivisorZeroValue z).re = 1 / 2)
    (hleft : ‖dusartBoxLowPhaseSum m (s / (1 - (m + 3 : ℕ) * s)) u T
      (Real.log (x * (1 - (m + 3 : ℕ) * s)) - u)‖ ≤ L)
    (hright : ‖dusartBoxLowPhaseSum m s v T (Real.log x - v)‖ ≤ U) :
    |Chebyshev.psi x - x| / x ≤
      max ((1 - (m + 3 : ℕ) * s) *
        dusartBoxPhaseBudget m (s / (1 - (m + 3 : ℕ) * s))
          (x * (1 - (m + 3 : ℕ) * s)) T L)
        (dusartBoxPhaseBudget m s x T U) + (m + 3 : ℕ) * s / 2 :=
  dusart_abs_psi_div_le_phase m u v hs hx hT hq hy hline hleft hright
