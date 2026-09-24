import PrimeFactorUnimodality.Helpers.Analytic.PlattDirichletConvolution
import PrimeFactorUnimodality.Mathlib.Analysis.Fourier.CorrelationTrace

set_option autoImplicit false

/-! # Rounded shared convolution encloses the actual finite Dirichlet prefix

Coefficient products and colliding bucket accumulation feed the forward input
enclosures. The complete shared-trace theorem then gives the finite prefix,
with every forward, product, accumulation and inverse error retained. A last
local rounding check covers normalization and subtraction of the pole input.
-/

open Finset
open scoped Nat

namespace PrimeFactorUnimodality

noncomputable section

/-- Rounded coefficient rows and bucket sums supply the left transform's input error. -/
theorem norm_plattDirichletTaylorBucket_sub_rounded_le {N : ℕ} [NeZero N]
    (J r : ℕ) (bin : ℕ → ZMod N) (c : ℕ → ℂ) (w : ℕ → ℝ)
    {p : ℕ → ℂ} {μ : ℕ → ℝ} {b : ℂ} {δ : ℝ}
    (hp : ∀ i ∈ range J, ‖c i * ((w i ^ r / (r ! : ℝ) : ℝ) : ℂ) - p i‖ ≤ μ i)
    (l : ZMod N) (hb : ‖ZMod.bucketCoefficients (range J) bin p l - b‖ ≤ δ) :
    ‖plattDirichletTaylorBuckets J bin c w r l - b‖ ≤
      (∑ i ∈ (range J).filter (fun i => bin i = l), μ i) + δ :=
  ZMod.norm_bucketCoefficients_sub_rounded_le (range J) bin hp l hb

/-- The shared computation supplies the finite-prefix bound, rather than assuming it. -/
theorem norm_plattApproxDirichletPrefix_sub_correlationTrace_le {n : ℕ}
    (J K : ℕ) (bin : ℕ → ZMod (2 ^ n)) (c : ℕ → ℂ) (w : ℕ → ℝ)
    (Q : ℕ → ZMod (2 ^ n) → ℂ) {t : Fourier.CorrelationTrace ℕ n}
    {α β : ℕ → ZMod (2 ^ n) → ℝ}
    (ht : t.Valid (range K) (plattDirichletTaylorBuckets J bin c w) Q α β)
    (j : ZMod (2 ^ n)) :
    ‖plattApproxDirichletPrefix J K c (fun i r => Q r (j + bin i)) w - t.value j‖ ≤
      t.error (range K) α β := by
  rw [plattApproxDirichletPrefix_eq_correlations]
  exact ht.norm_sum_correlation_sub_le j

/-- Final scaling and pole subtraction rounding is added once to the complete trace error. -/
theorem norm_plattApproxDirichletPrefix_sub_pole_trace_le {n : ℕ}
    (J K : ℕ) (bin : ℕ → ZMod (2 ^ n)) (c : ℕ → ℂ) (w : ℕ → ℝ)
    (Q : ℕ → ZMod (2 ^ n) → ℂ) {t : Fourier.CorrelationTrace ℕ n}
    {α β : ℕ → ZMod (2 ^ n) → ℝ}
    (ht : t.Valid (range K) (plattDirichletTaylorBuckets J bin c w) Q α β)
    (j : ZMod (2 ^ n)) {ρ z : ℂ} {δ : ℝ} (hz : ‖t.value j - ρ - z‖ ≤ δ) :
    ‖plattApproxDirichletPrefix J K c (fun i r => Q r (j + bin i)) w - ρ - z‖ ≤
      t.error (range K) α β + δ := by
  have hp := norm_plattApproxDirichletPrefix_sub_correlationTrace_le J K bin c w Q ht j
  have he : plattApproxDirichletPrefix J K c (fun i r => Q r (j + bin i)) w - ρ -
      (t.value j - ρ) =
      plattApproxDirichletPrefix J K c (fun i r => Q r (j + bin i)) w - t.value j := by ring
  apply (norm_sub_le_norm_sub_add_norm_sub _ (t.value j - ρ) _).trans
  rw [he]
  exact add_le_add hp hz

end

end PrimeFactorUnimodality
