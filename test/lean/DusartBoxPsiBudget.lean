import PrimeFactorUnimodality.Helpers.Analytic.DusartBoxPsiBudget

/-! # Regressions for the actual psi budget

Keep every low-height input explicit, exercise a zero gap using the proved
critical strip, and retain the left-average condition and smoothing loss.
The pointwise estimates apply without excluding jumps of psi.
-/

namespace PrimeFactorUnimodality.Tests

open Chebyshev

example (m : ℕ) (h x T δ M : ℝ) :
    dusartBoxErrorBudget m h x T δ M =
      ((x + (m + 3 : ℕ) * h) * Real.exp (-δ * Real.log x)) * M +
        dusartBoxTailFactor m h x T * (4 * xiLehmanHighBound (T / 2) (T / 2)) +
        1 / (2 * (x ^ 2 - 1)) + Real.log (2 * Real.pi) := rfl

example (m : ℕ) {h x T δ M : ℝ}
    (hh : 0 < h) (hx : 1 < x) (hT : 10 ^ 9 ≤ T) (hδ : 0 ≤ δ)
    (hg : ∀ p ∈ xiLowHeightIndices T, (riemannXiDivisorZeroValue p).re ≤ 1 - δ)
    (hM : (∑ p ∈ xiLowHeightIndices T, ‖(1 : ℂ) / riemannXiDivisorZeroValue p‖) ≤ M) :
    |dusartPsiAverageError (m + 3) h x| ≤ dusartBoxErrorBudget m h x T δ M :=
  abs_dusartPsiAverageError_le_budget m hh hx hT hδ hg hM

example (m : ℕ) {h x T : ℝ} (hh : 0 < h) (hx : 1 < x) (hT : 10 ^ 9 ≤ T) :
    |dusartPsiAverageError (m + 3) h x| ≤ dusartBoxErrorBudget m h x T 0
      (∑ p ∈ xiLowHeightIndices T, ‖(1 : ℂ) / riemannXiDivisorZeroValue p‖) := by
  apply abs_dusartPsiAverageError_le_budget m hh hx hT (by norm_num) _ le_rfl
  intro p _
  simpa only [sub_zero] using
    (riemannXi_zero_mem_critical_strip (riemannXiDivisorZeroValue_eq_zero p)).2

example (m : ℕ) {h x T δ M : ℝ}
    (hh : 0 < h) (hx : 1 < x - (m + 3 : ℕ) * h) (hT : 10 ^ 9 ≤ T) (hδ : 0 ≤ δ)
    (hg : ∀ p ∈ xiLowHeightIndices T, (riemannXiDivisorZeroValue p).re ≤ 1 - δ)
    (hM : (∑ p ∈ xiLowHeightIndices T, ‖(1 : ℂ) / riemannXiDivisorZeroValue p‖) ≤ M) :
    |ψ x - x| ≤ max (dusartBoxErrorBudget m h (x - (m + 3 : ℕ) * h) T δ M)
      (dusartBoxErrorBudget m h x T δ M) + (m + 3 : ℕ) * h / 2 :=
  abs_psi_sub_le_dusartBoxBudget m hh hx hT hδ hg hM

example (m : ℕ) {h x T δ M : ℝ}
    (hh : 0 < h) (hx : 1 < x - (m + 3 : ℕ) * h) (hT : 10 ^ 9 ≤ T) (hδ : 0 ≤ δ)
    (hg : ∀ p ∈ xiLowHeightIndices T, (riemannXiDivisorZeroValue p).re ≤ 1 - δ)
    (hM : (∑ p ∈ xiLowHeightIndices T, ‖(1 : ℂ) / riemannXiDivisorZeroValue p‖) ≤ M) :
    |ψ x / x - 1| ≤
      (max (dusartBoxErrorBudget m h (x - (m + 3 : ℕ) * h) T δ M)
        (dusartBoxErrorBudget m h x T δ M) + (m + 3 : ℕ) * h / 2) / x :=
  abs_psi_div_sub_one_le_dusartBoxBudget m hh hx hT hδ hg hM

end PrimeFactorUnimodality.Tests
