import PrimeFactorUnimodality.Helpers.Analytic.DusartBoxLogFourth
import PrimeFactorUnimodality.Helpers.Analytic.XiLowReciprocalNormBound

/-! # The Dusart box budget with its reciprocal mass discharged by counting

The gap controls the small prefix through same-height reflection; the
proved counting envelope controls the reciprocal-norm window. Substituting
that explicit bound removes the independent mass input from the actual psi
estimate and the fixed-cutoff theta interface. The low-height gap itself and
the uniform scalar parameter budget remain to be proved.
-/

namespace PrimeFactorUnimodality

noncomputable section

open Chebyshev

/-- The previous box budget with the norm-mass coefficient now given explicitly. -/
def dusartBoxCountingErrorBudget (m : ℕ) (h x a T δ : ℝ) : ℝ :=
  dusartBoxErrorBudget m h x T δ (xiLowReciprocalNormBound a T δ)

/-- The actual psi average no longer needs an independently supplied low mass. -/
theorem abs_dusartPsiAverageError_le_countingBudget (m : ℕ) {h x a T δ : ℝ}
    (hh : 0 < h) (hx : 1 < x) (ha : 10 ≤ a) (haT : a < T)
    (hT : 10 ^ 9 ≤ T) (hδ : 0 < δ)
    (hgap : ∀ p ∈ xiLowHeightIndices T, (riemannXiDivisorZeroValue p).re ≤ 1 - δ) :
    |dusartPsiAverageError (m + 3) h x| ≤ dusartBoxCountingErrorBudget m h x a T δ :=
  abs_dusartPsiAverageError_le_budget m hh hx hT hδ.le hgap
    (sum_xi_low_reciprocal_norm_le_explicit ha haT hδ hgap)

/-- The two actual averages give the pointwise estimate, with the exact smoothing loss. -/
theorem abs_psi_sub_le_dusartBoxCountingBudget (m : ℕ) {h x a T δ : ℝ}
    (hh : 0 < h) (hx : 1 < x - (m + 3 : ℕ) * h) (ha : 10 ≤ a) (haT : a < T)
    (hT : 10 ^ 9 ≤ T) (hδ : 0 < δ)
    (hgap : ∀ p ∈ xiLowHeightIndices T, (riemannXiDivisorZeroValue p).re ≤ 1 - δ) :
    |ψ x - x| ≤
      max (dusartBoxCountingErrorBudget m h (x - (m + 3 : ℕ) * h) a T δ)
        (dusartBoxCountingErrorBudget m h x a T δ) + (m + 3 : ℕ) * h / 2 :=
  abs_psi_sub_le_dusartBoxBudget m hh hx hT hδ.le hgap
    (sum_xi_low_reciprocal_norm_le_explicit ha haT hδ hgap)

/-- The remaining uniform gap-and-scalar obligation, with no reciprocal-mass hypothesis. -/
def HasDusartBoxCountingBudget (A X : ℝ) : Prop :=
  ∀ x : ℝ, X ≤ x → ∃ (m : ℕ) (h a T δ : ℝ),
    0 < h ∧ 1 < x - (m + 3 : ℕ) * h ∧ 10 ≤ a ∧ a < T ∧ 10 ^ 9 ≤ T ∧ 0 < δ ∧
      (∀ p ∈ xiLowHeightIndices T, (riemannXiDivisorZeroValue p).re ≤ 1 - δ) ∧
      max (dusartBoxCountingErrorBudget m h (x - (m + 3 : ℕ) * h) a T δ)
        (dusartBoxCountingErrorBudget m h x a T δ) + (m + 3 : ℕ) * h / 2 ≤
          A * x / (Real.log x) ^ 4

/-- The proved counting bound supplies the previously explicit mass input at every point. -/
theorem hasDusartBoxLogFourthBudget_of_counting {A X : ℝ}
    (h : HasDusartBoxCountingBudget A X) : HasDusartBoxLogFourthBudget A X := by
  intro x hx
  obtain ⟨m, step, a, T, δ, hs, hl, ha, haT, hT, hδ, hg, hb⟩ := h x hx
  exact ⟨m, step, T, δ, xiLowReciprocalNormBound a T δ, hs, hl, hT, hδ.le, hg,
    sum_xi_low_reciprocal_norm_le_explicit ha haT hδ hg, hb⟩

/-- The general log-fourth psi provider inherits the proved mass estimate. -/
theorem hasPsiLogFourthError_of_dusartBoxCountingBudget {A X : ℝ}
    (h : HasDusartBoxCountingBudget A X) : HasPsiLogFourthError A X :=
  hasPsiLogFourthError_of_dusartBoxBudget (hasDusartBoxLogFourthBudget_of_counting h)

/-- The exact fixed-cutoff theta target with only gap and scalar inputs remaining. -/
theorem hasThetaLogFourthError_648_of_dusartBoxCountingBudget
    (h : HasDusartBoxCountingBudget (1 / 2) (4e18)) :
    HasThetaLogFourthError (648 / 1000) (4e18) :=
  hasThetaLogFourthError_648_of_dusartBoxBudget (hasDusartBoxLogFourthBudget_of_counting h)

end

end PrimeFactorUnimodality
