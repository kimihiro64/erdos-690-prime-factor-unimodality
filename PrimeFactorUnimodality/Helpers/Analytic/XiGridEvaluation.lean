import PrimeFactorUnimodality.Helpers.Analytic.XiSignRows
import PrimeFactorUnimodality.Helpers.Analytic.XiStirlingPhase
import PrimeFactorUnimodality.Helpers.Analytic.ZetaGridEvaluation

/-! # Actual xi sign rows from shared Fourier evaluation

The existing phase and normalized-xi theorems consume the complete grid
error. Sign changes feed the existing verifier without a zero or RH premise.
Completeness still requires the separate Turing margin.
-/

namespace PrimeFactorUnimodality

noncomputable section

open Complex

/-- The real normalized approximation after the evaluated xi phase rotation. -/
def ZetaGridPoint.xiApprox (p : ZetaGridPoint) (d : ZetaGridBlock) (θ : ℝ) : ℝ :=
  (exp (I * θ) * p.value d).re

/-- Complete grid error together with analytic and evaluated phase errors. -/
def ZetaGridPoint.xiError (p : ZetaGridPoint) (d : ZetaGridBlock) (δ : ℝ) : ℝ :=
  p.error d + ‖p.value d‖ * (1 / 10 + δ)

/-- The full grid and phase errors bound actual normalized xi. -/
theorem ZetaGridPoint.Valid.abs_xi_sub_approx_le {d : ZetaGridBlock} (hd : d.Valid)
    {p : ZetaGridPoint} (hp : p.Valid d) {θ δ : ℝ}
    (hθ : |turingStirlingPhase (p.height d) - θ| ≤ δ) :
    |xiNormalizedValue (p.height d) - p.xiApprox d θ| ≤ p.xiError d δ := by
  exact abs_xiNormalizedValue_sub_approx_le (hp.norm_zeta_sub_value_le hd)
    ((abs_sub_le _ _ _).trans
      (add_le_add (abs_turingCountingPhase_sub_stirling_le (p.height d)) hθ))

/-- Either sign orientation supplies the actual rational-endpoint sign-row verifier. -/
theorem XiSignRow.valid_of_grid_endpoints {row : XiSignRow} (hwidth : row.lower < row.upper)
    {d e : ZetaGridBlock} (hd : d.Valid) (he : e.Valid)
    {p q : ZetaGridPoint} (hp : p.Valid d) (hq : q.Valid e)
    (hlower : p.height d = (row.lower : ℝ)) (hupper : q.height e = (row.upper : ℝ))
    {θ φ δ ε : ℝ} (hθ : |turingStirlingPhase (p.height d) - θ| ≤ δ)
    (hφ : |turingStirlingPhase (q.height e) - φ| ≤ ε)
    (hmargin : (p.xiError d δ < p.xiApprox d θ ∧ q.xiApprox e φ < -q.xiError e ε) ∨
      (p.xiApprox d θ < -p.xiError d δ ∧ q.xiError e ε < q.xiApprox e φ)) : row.Valid := by
  have hphasep := (abs_sub_le (turingCountingPhase (p.height d))
    (turingStirlingPhase (p.height d)) θ).trans
      (add_le_add (abs_turingCountingPhase_sub_stirling_le _) hθ)
  have hphaseq := (abs_sub_le (turingCountingPhase (q.height e))
    (turingStirlingPhase (q.height e)) φ).trans
      (add_le_add (abs_turingCountingPhase_sub_stirling_le _) hφ)
  refine ⟨hwidth, ?_⟩
  rw [← hlower, ← hupper]
  rcases hmargin with ⟨hpos, hneg⟩ | ⟨hneg, hpos⟩
  · exact mul_neg_of_pos_of_neg
      (xiCriticalLineValue_pos_of_approx (hp.norm_zeta_sub_value_le hd) hphasep hpos)
      (xiCriticalLineValue_neg_of_approx (hq.norm_zeta_sub_value_le he) hphaseq hneg)
  · exact mul_neg_of_neg_of_pos
      (xiCriticalLineValue_neg_of_approx (hp.norm_zeta_sub_value_le hd) hphasep hneg)
      (xiCriticalLineValue_pos_of_approx (hq.norm_zeta_sub_value_le he) hphaseq hpos)

end

end PrimeFactorUnimodality
