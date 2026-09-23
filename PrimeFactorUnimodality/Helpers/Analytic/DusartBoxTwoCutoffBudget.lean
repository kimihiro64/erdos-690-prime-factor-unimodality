import PrimeFactorUnimodality.Helpers.Analytic.DusartBoxCountingBudget
import PrimeFactorUnimodality.Helpers.Analytic.DusartBoxTwoCutoffs

/-! # Pointwise Dusart bounds with a fixed low-height input

Only zeros below the fixed `H` need an independently proved location bound.
The intermediate band and infinite tail have already been bounded using
the unconditional initial region and counting theorem. The remaining scalar
budget may vary its smoothing order, step, and upper cutoff with `x`.
The final theorems do not assert either the low input or the scalar budget.
-/

namespace PrimeFactorUnimodality

noncomputable section

open Chebyshev

/-- The complete actual error budget, including the negative-even and endpoint corrections. -/
def dusartBoxTwoCutoffErrorBudget (m : ℕ) (h x a H T δ : ℝ) : ℝ :=
  dusartBoxTwoCutoffZeroBudget m h x a H T δ +
    1 / (2 * (x ^ 2 - 1)) + Real.log (2 * Real.pi)

/-- At equal cutoffs the band costs nothing: the original counting budget is recovered exactly. -/
@[simp] theorem dusartBoxTwoCutoffErrorBudget_self (m : ℕ) (h x a H δ : ℝ) :
    dusartBoxTwoCutoffErrorBudget m h x a H H δ =
      dusartBoxCountingErrorBudget m h x a H δ := by
  simp [dusartBoxTwoCutoffErrorBudget, dusartBoxTwoCutoffZeroBudget,
    dusartBoxCountingErrorBudget, dusartBoxErrorBudget]

/-- The true average inherits the two-cutoff estimate with both corrections retained. -/
theorem abs_dusartPsiAverageError_le_twoCutoffBudget (m : ℕ) {h x a H T δ : ℝ}
    (hh : 0 < h) (hx : 1 < x) (ha : 10 ≤ a) (haH : a < H)
    (hH : 10 ^ 9 ≤ H) (hHT : H ≤ T) (hδ : 0 < δ)
    (hgap : ∀ p ∈ xiLowHeightIndices H, (riemannXiDivisorZeroValue p).re ≤ 1 - δ) :
    |dusartPsiAverageError (m + 3) h x| ≤ dusartBoxTwoCutoffErrorBudget m h x a H T δ :=
  (abs_dusartPsiAverageError_le_zero_sum m hh hx).trans
    (add_le_add (add_le_add
      (norm_smoothedXiPairedSum_box_le_two_cutoffs m hh hx ha haH hH hHT hδ hgap)
      le_rfl) le_rfl)

/-- Both adjacent averages give a pointwise estimate, including at prime-power jumps. -/
theorem abs_psi_sub_le_dusartBoxTwoCutoffBudget (m : ℕ) {h x a H T δ : ℝ}
    (hh : 0 < h) (hx : 1 < x - (m + 3 : ℕ) * h) (ha : 10 ≤ a) (haH : a < H)
    (hH : 10 ^ 9 ≤ H) (hHT : H ≤ T) (hδ : 0 < δ)
    (hgap : ∀ p ∈ xiLowHeightIndices H, (riemannXiDivisorZeroValue p).re ≤ 1 - δ) :
    |ψ x - x| ≤
      max (dusartBoxTwoCutoffErrorBudget m h (x - (m + 3 : ℕ) * h) a H T δ)
        (dusartBoxTwoCutoffErrorBudget m h x a H T δ) + (m + 3 : ℕ) * h / 2 := by
  have hx' : 1 < x := by
    have hn : 0 ≤ (m + 3 : ℕ) * h := mul_nonneg (Nat.cast_nonneg _) hh.le
    linarith
  exact dusart_abs_psi_error_le_of_averages (m + 3) hh
    ((abs_dusartPsiAverageError_le_twoCutoffBudget m hh hx ha haH hH hHT hδ hgap).trans
      (le_max_left _ _))
    ((abs_dusartPsiAverageError_le_twoCutoffBudget m hh hx' ha haH hH hHT hδ hgap).trans
      (le_max_right _ _))

/-- A purely scalar remaining obligation, with the low-height cutoff and gap fixed. -/
def HasDusartTwoCutoffScalarBudget (A X H δ : ℝ) : Prop :=
  ∀ x : ℝ, X ≤ x → ∃ (m : ℕ) (h a T : ℝ),
    0 < h ∧ 1 < x - (m + 3 : ℕ) * h ∧ 10 ≤ a ∧ a < H ∧ H ≤ T ∧
      max (dusartBoxTwoCutoffErrorBudget m h (x - (m + 3 : ℕ) * h) a H T δ)
        (dusartBoxTwoCutoffErrorBudget m h x a H T δ) + (m + 3 : ℕ) * h / 2 ≤
          A * x / (Real.log x) ^ 4

/-- A single fixed low-zero theorem suffices for the entire uniform psi range. -/
theorem hasPsiLogFourthError_of_twoCutoffBudget {A X H δ : ℝ}
    (hH : 10 ^ 9 ≤ H) (hδ : 0 < δ)
    (hgap : ∀ p ∈ xiLowHeightIndices H, (riemannXiDivisorZeroValue p).re ≤ 1 - δ)
    (h : HasDusartTwoCutoffScalarBudget A X H δ) : HasPsiLogFourthError A X := by
  intro x hx
  obtain ⟨m, step, a, T, hs, hl, ha, haH, hHT, hb⟩ := h x hx
  exact (abs_psi_sub_le_dusartBoxTwoCutoffBudget m hs hl ha haH hH hHT hδ hgap).trans hb

/-- The same fixed input and scalar proof deliver the exact required theta coefficient. -/
theorem hasThetaLogFourthError_648_of_twoCutoffBudget {H δ : ℝ}
    (hH : 10 ^ 9 ≤ H) (hδ : 0 < δ)
    (hgap : ∀ p ∈ xiLowHeightIndices H, (riemannXiDivisorZeroValue p).re ≤ 1 - δ)
    (h : HasDusartTwoCutoffScalarBudget (1 / 2) (4e18) H δ) :
    HasThetaLogFourthError (648 / 1000) (4e18) := by
  convert hasThetaLogFourthError_of_psiLogFourthError_sharp le_rfl
    (hasPsiLogFourthError_of_twoCutoffBudget hH hδ hgap h) using 1
  norm_num

end

end PrimeFactorUnimodality
