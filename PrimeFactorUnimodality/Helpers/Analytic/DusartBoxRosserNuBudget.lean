import PrimeFactorUnimodality.Helpers.Analytic.DusartBoxRosserBandBudget
import PrimeFactorUnimodality.Helpers.Analytic.XiRosserNuTail
import PrimeFactorUnimodality.Helpers.Analytic.XiRosserNuWindow

/-! # The actual psi estimate with the Rosser exponent and cutoff chosen

Set `X=sqrt(log(x)/R)`, `T=exp(nu*X)` and `p=m+4-1/nu^2`. The single
condition `(m+3)*nu^2>1` discharges the exponent and decreasing-tail
conditions; `nu<=1` supplies the increasing window condition. Each of
the two pointwise averages may use its own cutoff at the same parameter.
-/

namespace PrimeFactorUnimodality

noncomputable section

open Chebyshev Real

/-- The complete elementary budget without auxiliary exponent or cutoff choices. -/
def dusartBoxRosserNuErrorBudget (m : ℕ) (h x R ν a H δ : ℝ) : ℝ :=
  let X := sqrt (Real.log x / R)
  ((x + (m + 3 : ℕ) * h) * exp (-δ * Real.log x)) * xiLowReciprocalNormBound a H δ +
    (x + (m + 3 : ℕ) * h) * (2 * xiRosserNuWindowBound X ν) +
    (2 ^ (m + 3) * (x + (m + 3 : ℕ) * h) ^ (m + 4) / h ^ (m + 3)) *
      xiRosserNuTailBound X (m + 4 : ℕ) ν + 1 / (2 * (x ^ 2 - 1)) + Real.log (2 * π)

/-- The explicit parameter choice majorizes the previous complete two-kernel budget. -/
theorem dusartBoxRosserBandErrorBudget_le_nu (m : ℕ) {h x R ν a H δ : ℝ}
    (hh : 0 < h) (hx : 1 < x) (hR : 0 < R) (hν : 0 < ν)
    (hmargin : 1 < (m + 3 : ℕ) * ν ^ 2) (hH : 20 ≤ H)
    (hHT : H ≤ exp (ν * sqrt (Real.log x / R))) :
    dusartBoxRosserBandErrorBudget m h x R ((m + 4 : ℕ) - 1 / ν ^ 2) a H
        (exp (ν * sqrt (Real.log x / R))) δ ≤ dusartBoxRosserNuErrorBudget m h x R ν a H δ := by
  let X := sqrt (Real.log x / R)
  have hX : 0 < X := sqrt_pos.mpr (div_pos (Real.log_pos hx) hR)
  have hXsq : X ^ 2 = Real.log x / R := sq_sqrt (div_nonneg (Real.log_pos hx).le hR.le)
  have hq : ((m + 4 : ℕ) : ℝ) - 1 = (m + 3 : ℕ) := by push_cast; ring
  have hmarg : 1 < (((m + 4 : ℕ) : ℝ) - 1) * ν ^ 2 := by simpa only [hq] using hmargin
  have hb := xiRosserIncreasingBandBound_le_nu hX hν hH hHT
  rw [hXsq] at hb
  have he : dusartBoxRosserClosedTailBudget m h x R ((m + 4 : ℕ) - 1 / ν ^ 2)
      (exp (ν * X)) =
      (2 ^ (m + 3) * (x + (m + 3 : ℕ) * h) ^ (m + 4) / h ^ (m + 3)) *
        xiRosserNuTailBound X (m + 4 : ℕ) ν := by
    unfold dusartBoxRosserClosedTailBudget
    congr 1
    rw [← hXsq, xiRosserClosedTailBound_eq_nu hX hν hmarg]
  have hx0 : 0 < x := lt_trans zero_lt_one hx
  unfold dusartBoxRosserBandErrorBudget dusartBoxRosserNuErrorBudget
  rw [he]
  exact add_le_add (add_le_add (add_le_add
    (add_le_add le_rfl (mul_le_mul_of_nonneg_left hb (by positivity))) le_rfl) le_rfl) le_rfl

/-- The actual average has the parameterized bound, with both turning conditions discharged. -/
theorem abs_dusartPsiAverageError_le_rosserNuBudget (m : ℕ) {h x R ν a H δ : ℝ}
    (hh : 0 < h) (hx : 1 < x) (hR : 0 < R) (hν : 0 < ν) (hν1 : ν ≤ 1)
    (hmargin : 1 < (m + 3 : ℕ) * ν ^ 2)
    (ha : 10 ≤ a) (haH : a < H) (hH : 20 ≤ H) (hδ : 0 < δ)
    (hHT : H ≤ exp (ν * sqrt (Real.log x / R)))
    (hgap : ∀ z ∈ xiLowHeightIndices H, (riemannXiDivisorZeroValue z).re ≤ 1 - δ)
    (hreg : ∀ z : RiemannXiDivisorZeroIndex, H ≤ |(riemannXiDivisorZeroValue z).im| →
      (riemannXiDivisorZeroValue z).re ≤
        1 - 1 / (R * Real.log |(riemannXiDivisorZeroValue z).im|)) :
    |dusartPsiAverageError (m + 3) h x| ≤ dusartBoxRosserNuErrorBudget m h x R ν a H δ := by
  let X := sqrt (Real.log x / R)
  have hX : 0 < X := sqrt_pos.mpr (div_pos (Real.log_pos hx) hR)
  have hXsq : X ^ 2 = Real.log x / R := sq_sqrt (div_nonneg (Real.log_pos hx).le hR.le)
  have hq : ((m + 4 : ℕ) : ℝ) - 1 = (m + 3 : ℕ) := by push_cast; ring
  have hmarg : 1 < (((m + 4 : ℕ) : ℝ) - 1) * ν ^ 2 := by simpa only [hq] using hmargin
  have hp := logDampedPower_nu_exponent_mem hν hmarg
  have hinc : exp (ν * X) ≤ exp (sqrt (Real.log x / R)) :=
    exp_le_exp.mpr (by change ν * X ≤ X; nlinarith)
  have hdec : exp (sqrt ((Real.log x / R) / (m + 4 : ℕ))) ≤ exp (ν * X) := by
    rw [← hXsq]
    exact logDampedPower_nu_turn_le hX hν hmarg
  exact (abs_dusartPsiAverageError_le_rosserBandBudget m hh hx hR hp.1 hp.2
    ha haH hH hHT hδ hgap hinc hdec hreg).trans
      (dusartBoxRosserBandErrorBudget_le_nu m hh hx hR hν hmargin hH hHT)

/-- The pointwise bound uses the same parameter but the appropriate cutoff at each average. -/
theorem abs_psi_sub_le_dusartBoxRosserNuBudget (m : ℕ) {h x R ν a H δ : ℝ}
    (hh : 0 < h) (hx : 1 < x - (m + 3 : ℕ) * h) (hR : 0 < R)
    (hν : 0 < ν) (hν1 : ν ≤ 1) (hmargin : 1 < (m + 3 : ℕ) * ν ^ 2)
    (ha : 10 ≤ a) (haH : a < H) (hH : 20 ≤ H) (hδ : 0 < δ)
    (hHT : H ≤ exp (ν * sqrt (Real.log (x - (m + 3 : ℕ) * h) / R)))
    (hgap : ∀ z ∈ xiLowHeightIndices H, (riemannXiDivisorZeroValue z).re ≤ 1 - δ)
    (hreg : ∀ z : RiemannXiDivisorZeroIndex, H ≤ |(riemannXiDivisorZeroValue z).im| →
      (riemannXiDivisorZeroValue z).re ≤
        1 - 1 / (R * Real.log |(riemannXiDivisorZeroValue z).im|)) :
    |ψ x - x| ≤
      max (dusartBoxRosserNuErrorBudget m h (x - (m + 3 : ℕ) * h) R ν a H δ)
        (dusartBoxRosserNuErrorBudget m h x R ν a H δ) + (m + 3 : ℕ) * h / 2 := by
  have hleft : x - (m + 3 : ℕ) * h ≤ x :=
    sub_le_self _ (mul_nonneg (Nat.cast_nonneg _) hh.le)
  have hx' : 1 < x := hx.trans_le hleft
  have hlog := div_le_div_of_nonneg_right
    (Real.log_le_log (lt_trans zero_lt_one hx) hleft) hR.le
  have hHT' := hHT.trans (exp_le_exp.mpr
    (mul_le_mul_of_nonneg_left (sqrt_le_sqrt hlog) hν.le))
  exact dusart_abs_psi_error_le_of_averages (m + 3) hh
    ((abs_dusartPsiAverageError_le_rosserNuBudget m hh hx hR hν hν1 hmargin
      ha haH hH hδ hHT hgap hreg).trans (le_max_left _ _))
    ((abs_dusartPsiAverageError_le_rosserNuBudget m hh hx' hR hν hν1 hmargin
      ha haH hH hδ hHT' hgap hreg).trans (le_max_right _ _))

end

end PrimeFactorUnimodality
