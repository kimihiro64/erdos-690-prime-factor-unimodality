import PrimeFactorUnimodality.Helpers.Analytic.DusartBoxPsiBudget
import PrimeFactorUnimodality.Helpers.Analytic.ThetaFromPsi

/-! # Connecting box estimates to the fixed log-fourth provider interfaces

The remaining inputs are actual low-zero information and scalar budgets
for admissible box parameters at every point above the stated cutoff.
They no longer include an assumed explicit formula or psi estimate. The
existing sharp prime-power transfer spends `148/1000` of the theta budget,
so the target `648/1000` needs a psi budget of `1/2` from `4e18` onward.
This module proves the transfer; it does not assert the remaining inputs.
-/

namespace PrimeFactorUnimodality

noncomputable section

/-- Admissible parameters, low-zero inputs, and a scalar bound at every point. -/
def HasDusartBoxLogFourthBudget (A X : ℝ) : Prop :=
  ∀ x : ℝ, X ≤ x → ∃ (m : ℕ) (h T δ M : ℝ),
    0 < h ∧ 1 < x - (m + 3 : ℕ) * h ∧ 10 ^ 9 ≤ T ∧ 0 ≤ δ ∧
      (∀ p ∈ xiLowHeightIndices T, (riemannXiDivisorZeroValue p).re ≤ 1 - δ) ∧
      (∑ p ∈ xiLowHeightIndices T, ‖(1 : ℂ) / riemannXiDivisorZeroValue p‖) ≤ M ∧
      max (dusartBoxErrorBudget m h (x - (m + 3 : ℕ) * h) T δ M)
        (dusartBoxErrorBudget m h x T δ M) + (m + 3 : ℕ) * h / 2 ≤
          A * x / (Real.log x) ^ 4

/-- The exact explicit formula and pointwise conversion discharge the psi provider. -/
theorem hasPsiLogFourthError_of_dusartBoxBudget {A X : ℝ}
    (h : HasDusartBoxLogFourthBudget A X) : HasPsiLogFourthError A X := by
  intro x hx
  obtain ⟨m, step, T, δ, M, hs, hl, hT, hδ, hg, hM, hb⟩ := h x hx
  exact (abs_psi_sub_le_dusartBoxBudget m hs hl hT hδ hg hM).trans hb

/-- Transfer the actual box psi bound through the existing sharp prime-power correction. -/
theorem hasThetaLogFourthError_of_dusartBoxBudget {A X : ℝ}
    (hX : (4e18 : ℝ) ≤ X) (h : HasDusartBoxLogFourthBudget A X) :
    HasThetaLogFourthError (A + 148 / 1000) X :=
  hasThetaLogFourthError_of_psiLogFourthError_sharp hX
    (hasPsiLogFourthError_of_dusartBoxBudget h)

/-- The exact fixed-cutoff theta target, once the named numerical and low-zero inputs are proved. -/
theorem hasThetaLogFourthError_648_of_dusartBoxBudget
    (h : HasDusartBoxLogFourthBudget (1 / 2) (4e18)) :
    HasThetaLogFourthError (648 / 1000) (4e18) := by
  convert hasThetaLogFourthError_of_dusartBoxBudget le_rfl h using 1
  norm_num

end

end PrimeFactorUnimodality
