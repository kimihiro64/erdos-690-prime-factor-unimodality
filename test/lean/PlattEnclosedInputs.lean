import PrimeFactorUnimodality.Helpers.Analytic.PlattDirichletConvolution
import PrimeFactorUnimodality.Helpers.Analytic.PlattDirichletPhase

/-! Enclosed inputs retain signed shifts, arbitrary orders and the empty-prefix boundaries. -/

open PrimeFactorUnimodality
open scoped FourierTransform

example (k : ℕ) (t₀ u w : ℝ) {h : ℝ} (hh : 0 < h) :
    ‖𝓕 (plattWindowKernel k t₀ h) (u + w)‖ ≤ plattFourierTaylorBound 0 k h |w| := by
  simpa [plattApproxTaylor, plattTaylorInputError] using
    norm_fourier_plattWindowKernel_sub_approx_input_le 0 k t₀ u w (u + w)
      (σ := 0) (q := fun _ => 0) (ε := fun _ => 0) hh (by simp) (by simp)

example (K : ℕ) (c : ℕ → ℂ) (q : ℕ → ℕ → ℂ) (w : ℕ → ℝ) :
    plattApproxDirichletPrefix 0 K c q w = 0 := by
  simp [plattApproxDirichletPrefix]

example {N : ℕ} [NeZero N] (J K : ℕ) (bin : ℕ → ZMod N)
    (c : ℕ → ℂ) (w : ℕ → ℝ) (Q : ℕ → ZMod N → ℂ) (j : ZMod N) :
    plattApproxDirichletPrefix J K c (fun n r => Q r (j + bin n)) w =
      (N : ℂ)⁻¹ * ZMod.dft (fun l => ∑ r ∈ Finset.range K,
        ZMod.dft (plattDirichletTaylorBuckets J bin c w r) (-l) * ZMod.dft (Q r) l) (-j) :=
  plattApproxDirichletPrefix_eq_single_inverse J K bin c w Q j

example {j : ℕ} (hj : 0 < j) :
    plattDirichletWeight 0 j = ((1 / Real.sqrt j : ℝ) : ℂ) := by
  simp [plattDirichletWeight_eq_rotation 0 hj]

example (j : ℕ) {L δ : ℝ} (hL : |Real.log ((j : ℝ) * Real.sqrt Real.pi) - L| ≤ δ) :
    |plattDirichletShift j - L / (2 * Real.pi)| ≤ δ / (2 * Real.pi) :=
  abs_plattDirichletShift_sub_le hL

example (t₀ : ℝ) {j : ℕ} (hj : 0 < j) {L δ a η : ℝ}
    (hL : |Real.log ((j : ℝ) * Real.sqrt Real.pi) - L| ≤ δ)
    (ha : |1 / Real.sqrt j - a| ≤ η) :
    ‖plattDirichletWeight t₀ j -
        Complex.exp (Complex.I * ((-t₀ * L : ℝ) : ℂ)) * (a : ℂ)‖ ≤
      η + |a| * (|t₀| * δ) :=
  norm_plattDirichletWeight_sub_log_approx_le t₀ hj hL ha
