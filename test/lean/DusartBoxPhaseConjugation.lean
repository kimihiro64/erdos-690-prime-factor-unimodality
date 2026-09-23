import PrimeFactorUnimodality.Helpers.Analytic.DusartBoxPhaseConjugation

/-! # The actual low sum uses positive data and has zero imaginary part -/

open PrimeFactorUnimodality Complex Finset
open scoped ComplexConjugate

example (m : ℕ) {s : ℝ} (hs : 0 ≤ s) (u : ℝ) (p : RiemannXiDivisorZeroIndex) :
    dusartBoxZeroCoefficient m s u (riemannXiDivisorConjugation p) =
      conj (dusartBoxZeroCoefficient m s u p) :=
  dusartBoxZeroCoefficient_conjugation m hs u p

example (m : ℕ) {s : ℝ} (hs : 0 ≤ s) (u T v : ℝ) :
    dusartBoxLowPhaseSum m s u T v =
      ((2 * (∑ p ∈ xiStrictPositiveHeightIndices T, dusartBoxZeroCoefficient m s u p *
        exp (I * ((v * (riemannXiDivisorZeroValue p).im : ℝ) : ℂ))).re : ℝ) : ℂ) :=
  dusartBoxLowPhaseSum_eq_twice_re m hs u T v

example (m : ℕ) {s : ℝ} (hs : 0 ≤ s) (u T v : ℝ) :
    (dusartBoxLowPhaseSum m s u T v).im = 0 := by
  rw [dusartBoxLowPhaseSum_eq_twice_re m hs, ofReal_im]

example (m : ℕ) (u T v : ℝ) :
    ‖dusartBoxLowPhaseSum m 0 u T v‖ =
      2 * |(∑ p ∈ xiStrictPositiveHeightIndices T, dusartBoxZeroCoefficient m 0 u p *
        exp (I * ((v * (riemannXiDivisorZeroValue p).im : ℝ) : ℂ))).re| :=
  norm_dusartBoxLowPhaseSum_eq m le_rfl u T v
