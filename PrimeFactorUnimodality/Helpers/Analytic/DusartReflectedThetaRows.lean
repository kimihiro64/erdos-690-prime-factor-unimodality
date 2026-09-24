import PrimeFactorUnimodality.Helpers.Analytic.DusartFrozenThetaCoverage
import PrimeFactorUnimodality.Helpers.Analytic.DusartReflectedLogBudget

/-! # The reflected scalar cap proves theta throughout compact row intervals

The row data, rational geometry, sharper-root conversion and ordered
coverage are shared with the original bound. Only the scalar allowance
changes. Each proved cap is reused for every real point of its interval.
-/

namespace PrimeFactorUnimodality

noncomputable section

open Real

namespace DusartFrozenThetaRow

/-- The reflected psi allowance and the unchanged sharper root correction. -/
def reflectedBudget (row : DusartFrozenThetaRow) (H : ℝ) : ℝ :=
  dusartReflectedLogPsiBound row.orderOffset row.step row.lower row.power H +
    (8 / 5) * exp (-(row.lower : ℝ) / 2)

/-- Shared row geometry with the reflected scalar cap. -/
structure ReflectedValid (row : DusartFrozenThetaRow) (H : ℝ) : Prop extends Geometry row where
  cap : row.reflectedBudget H * (row.upper : ℝ) ^ 2 ≤ (1 / 5 : ℝ)

/-- A reflected cap gives the required theta coefficient throughout the row's real interval. -/
theorem ReflectedValid.bound {row : DusartFrozenThetaRow} {H x : ℝ} (h : row.ReflectedValid H)
    (hH : 25000000 ≤ H) (hH₁ : H ≤ 1000000000)
    (hlow : ∀ z ∈ xiLowHeightIndices H,
      (riemannXiDivisorZeroValue z).re ≤ (1 / 2 : ℝ))
    (hreg : ∀ z : RiemannXiDivisorZeroIndex, H ≤ |(riemannXiDivisorZeroValue z).im| →
      (riemannXiDivisorZeroValue z).re ≤ 1 - 1 / (6 * log |(riemannXiDivisorZeroValue z).im|))
    (hxpos : 0 < x) (hxlo : (row.lower : ℝ) ≤ log x) (hxhi : log x ≤ row.upper) :
    |Chebyshev.theta x - x| ≤ (1 / 5 : ℝ) * x / log x ^ 2 := by
  let b : ℝ := row.lower
  let s : ℝ := row.step
  let t : ℝ := 1 - (row.orderOffset + 3 : ℕ) * s
  have hb : 25 ≤ b := by dsimp [b]; exact_mod_cast h.lower_ge
  have hb₁ : b ≤ 5000 := by dsimp [b]; exact_mod_cast h.ordered.trans h.upper_le
  have hs : 0 < s := by dsimp [s]; exact_mod_cast h.step_pos
  have hp : (1 : ℝ) < row.power := by exact_mod_cast h.power_gt
  have hpq : (row.power : ℝ) < (row.orderOffset + 4 : ℕ) := by exact_mod_cast h.power_lt
  obtain ⟨ht, hlog⟩ := shift_geometry h.lower_ge h.step_small
  have htpos : 0 < t := ht
  have he : log (exp b * t) = b + log t := by
    rw [log_mul (exp_pos b).ne' htpos.ne', log_exp]
  have hy : 1 < exp b * t := by
    have ha := add_one_le_exp (log (exp b * t))
    rw [exp_log (mul_pos (exp_pos b) htpos), he] at ha
    change 1 ≤ b + log t at hlog
    linarith
  have hxbase : exp b ≤ x := by simpa only [exp_log hxpos] using exp_le_exp.mpr hxlo
  have hpeak : exp (sqrt ((log (exp b) / 6) / (row.orderOffset + 4 : ℕ))) ≤ H := by
    rw [log_exp]
    exact dusartFrozen_peak_le row.orderOffset (by linarith) hb₁ hH
  have hpsi := abs_psi_sub_div_le_reflected_frozen row.orderOffset hs (exp_pos b) hxbase hy
    (by norm_num : (0 : ℝ) < 6) hp hpq (by norm_num : (10 : ℝ) ≤ 10)
    (by linarith : (10 : ℝ) < H) (by norm_num : (0 : ℝ) < 1 / 2)
    (by simpa only [show (1 - 1 / 2 : ℝ) = 1 / 2 by norm_num] using hlow) hpeak hreg
  have hbudget := dusartReflectedFrozenPsiBound_le_logPeak row.orderOffset hs
    (by linarith : 1 ≤ b) ht hlog hp hpq (by linarith : 10 ≤ H) hH₁
  exact h.toGeometry.theta_bound hxpos hxlo hxhi (hpsi.trans hbudget) h.cap

/-- The existing gap-free coverage chain assembles reflected rows without numerical replay. -/
theorem Covers.reflected_bound {a b : ℚ} {rows : List DusartFrozenThetaRow} {H x : ℝ}
    (h : Covers a b rows) (hvalid : ∀ row ∈ rows, row.ReflectedValid H)
    (hH : 25000000 ≤ H) (hH₁ : H ≤ 1000000000)
    (hlow : ∀ z ∈ xiLowHeightIndices H,
      (riemannXiDivisorZeroValue z).re ≤ (1 / 2 : ℝ))
    (hreg : ∀ z : RiemannXiDivisorZeroIndex, H ≤ |(riemannXiDivisorZeroValue z).im| →
      (riemannXiDivisorZeroValue z).re ≤
        1 - 1 / (6 * Real.log |(riemannXiDivisorZeroValue z).im|))
    (hx : 0 < x) (hlo : (a : ℝ) ≤ Real.log x) (hhi : Real.log x ≤ b) :
    |Chebyshev.theta x - x| ≤ (1 / 5 : ℝ) * x / Real.log x ^ 2 := by
  obtain ⟨row, hrow, hleft, hright⟩ := h.covers hlo hhi
  exact (hvalid row hrow).bound hH hH₁ hlow hreg hx hleft hright

end DusartFrozenThetaRow

end

end PrimeFactorUnimodality
