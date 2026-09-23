import PrimeFactorUnimodality.Helpers.Analytic.DusartBoxPsiError
import PrimeFactorUnimodality.Helpers.Analytic.DusartBoxZeroSplit

/-! # Quantitative box bounds for the actual Chebyshev error

The budget retains the low-zero gap and reciprocal-norm mass as explicit
inputs, combines the complete high tail and negative-even correction, and
includes the exact endpoint constant. Applying it to both adjacent averages
gives a pointwise bound even at jumps of psi. Numerical zero information and
the fixed-cutoff scalar certification are separate remaining obligations.
-/

namespace PrimeFactorUnimodality

noncomputable section

open Chebyshev

/-- Low zeros, the full high tail, all trivial zeros, and the endpoint constant. -/
def dusartBoxErrorBudget (m : ℕ) (h x T δ M : ℝ) : ℝ :=
  ((x + (m + 3 : ℕ) * h) * Real.exp (-δ * Real.log x)) * M +
    dusartBoxTailFactor m h x T * (4 * xiLehmanHighBound (T / 2) (T / 2)) +
    1 / (2 * (x ^ 2 - 1)) + Real.log (2 * Real.pi)

/-- The explicit scalar expression bounds the actual average, given the stated low inputs. -/
theorem abs_dusartPsiAverageError_le_budget (m : ℕ) {h x T δ M : ℝ}
    (hh : 0 < h) (hx : 1 < x) (hT : 10 ^ 9 ≤ T) (hδ : 0 ≤ δ)
    (hgap : ∀ p ∈ xiLowHeightIndices T, (riemannXiDivisorZeroValue p).re ≤ 1 - δ)
    (hmass : (∑ p ∈ xiLowHeightIndices T, ‖(1 : ℂ) / riemannXiDivisorZeroValue p‖) ≤ M) :
    |dusartPsiAverageError (m + 3) h x| ≤ dusartBoxErrorBudget m h x T δ M := by
  have hzero := norm_smoothedXiPairedSum_box_le_low_gap_add_high m hh hx hT hδ hgap
  have hx0 : 0 < x := lt_trans zero_lt_one hx
  have hcoef : 0 ≤ (x + (m + 3 : ℕ) * h) * Real.exp (-δ * Real.log x) := by positivity
  have hmass' := mul_le_mul_of_nonneg_left hmass hcoef
  exact (abs_dusartPsiAverageError_le_zero_sum m hh hx).trans
    (add_le_add (add_le_add
      (hzero.trans (add_le_add hmass' le_rfl)) le_rfl) le_rfl)

/-- Pointwise conversion of both adjacent box bounds, including jumps of psi. -/
theorem abs_psi_sub_le_dusartBoxBudget (m : ℕ) {h x T δ M : ℝ}
    (hh : 0 < h) (hx : 1 < x - (m + 3 : ℕ) * h) (hT : 10 ^ 9 ≤ T) (hδ : 0 ≤ δ)
    (hgap : ∀ p ∈ xiLowHeightIndices T, (riemannXiDivisorZeroValue p).re ≤ 1 - δ)
    (hmass : (∑ p ∈ xiLowHeightIndices T, ‖(1 : ℂ) / riemannXiDivisorZeroValue p‖) ≤ M) :
    |ψ x - x| ≤
      max (dusartBoxErrorBudget m h (x - (m + 3 : ℕ) * h) T δ M)
        (dusartBoxErrorBudget m h x T δ M) + (m + 3 : ℕ) * h / 2 := by
  have hx' : 1 < x := by
    have hn : 0 ≤ (m + 3 : ℕ) * h := mul_nonneg (Nat.cast_nonneg _) hh.le
    linarith
  exact dusart_abs_psi_error_le_of_averages (m + 3) hh
    ((abs_dusartPsiAverageError_le_budget m hh hx hT hδ hgap hmass).trans (le_max_left _ _))
    ((abs_dusartPsiAverageError_le_budget m hh hx' hT hδ hgap hmass).trans (le_max_right _ _))

/-- Divide the actual pointwise bound by the positive evaluation point. -/
theorem abs_psi_div_sub_one_le_dusartBoxBudget (m : ℕ) {h x T δ M : ℝ}
    (hh : 0 < h) (hx : 1 < x - (m + 3 : ℕ) * h) (hT : 10 ^ 9 ≤ T) (hδ : 0 ≤ δ)
    (hgap : ∀ p ∈ xiLowHeightIndices T, (riemannXiDivisorZeroValue p).re ≤ 1 - δ)
    (hmass : (∑ p ∈ xiLowHeightIndices T, ‖(1 : ℂ) / riemannXiDivisorZeroValue p‖) ≤ M) :
    |ψ x / x - 1| ≤
      (max (dusartBoxErrorBudget m h (x - (m + 3 : ℕ) * h) T δ M)
        (dusartBoxErrorBudget m h x T δ M) + (m + 3 : ℕ) * h / 2) / x := by
  have hx0 : 0 < x := by
    have hn : 0 ≤ (m + 3 : ℕ) * h := mul_nonneg (Nat.cast_nonneg _) hh.le
    linarith
  have he : ψ x / x - 1 = (ψ x - x) / x := by field_simp
  rw [he, abs_div, abs_of_pos hx0]
  exact div_le_div_of_nonneg_right
    (abs_psi_sub_le_dusartBoxBudget m hh hx hT hδ hgap hmass) hx0.le

end

end PrimeFactorUnimodality
