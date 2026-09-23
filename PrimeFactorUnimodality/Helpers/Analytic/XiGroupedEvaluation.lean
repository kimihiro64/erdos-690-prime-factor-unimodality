import PrimeFactorUnimodality.Helpers.Analytic.XiSignRows
import PrimeFactorUnimodality.Helpers.Analytic.XiStirlingPhase
import PrimeFactorUnimodality.Helpers.Analytic.ZetaGroupedEvaluation

/-! # Actual xi sign rows from shared zeta block evaluations

The existing normalized-xi and phase-error theorems consume the complete
grouped zeta bound. Endpoint signs feed the actual rational-row verifier;
finding these rows does not itself prove that every low zero was found.
-/

namespace PrimeFactorUnimodality

noncomputable section

open Complex

/-- The normalized real approximation after the evaluated phase rotation. -/
def ZetaGroupedPoint.xiApprox (p : ZetaGroupedPoint) (d : ZetaGroupedBlock) (θ : ℝ) : ℝ :=
  (exp (I * θ) * p.value d).re

/-- The complete zeta error and both analytic/numerical phase errors. -/
def ZetaGroupedPoint.xiError (p : ZetaGroupedPoint) (d : ZetaGroupedBlock) (δ : ℝ) : ℝ :=
  p.error d + ‖p.value d‖ * (1 / 10 + δ)

/-- A valid point bounds the actual normalized xi value, retaining every error source. -/
theorem ZetaGroupedPoint.Valid.abs_xi_sub_approx_le {d : ZetaGroupedBlock}
    (hd : d.Valid) {p : ZetaGroupedPoint} (hp : p.Valid d) {θ δ : ℝ}
    (hθ : |turingStirlingPhase (p.height d) - θ| ≤ δ) :
    |xiNormalizedValue (p.height d) - p.xiApprox d θ| ≤ p.xiError d δ := by
  apply abs_xiNormalizedValue_sub_approx_le (hp.norm_zeta_sub_value_le hd)
  exact (abs_sub_le _ _ _).trans
    (add_le_add (abs_turingCountingPhase_sub_stirling_le (p.height d)) hθ)

/-- A positive lower endpoint proves the actual xi sign. -/
theorem ZetaGroupedPoint.Valid.xi_pos {d : ZetaGroupedBlock}
    (hd : d.Valid) {p : ZetaGroupedPoint} (hp : p.Valid d) {θ δ : ℝ}
    (hθ : |turingStirlingPhase (p.height d) - θ| ≤ δ)
    (hmargin : p.xiError d δ < p.xiApprox d θ) : 0 < xiCriticalLineValue (p.height d) := by
  apply (xiCriticalLineValue_pos_iff_normalized _).mpr
  have h := (abs_le.mp (hp.abs_xi_sub_approx_le hd hθ)).1
  linarith

/-- A negative upper endpoint proves the opposite actual xi sign. -/
theorem ZetaGroupedPoint.Valid.xi_neg {d : ZetaGroupedBlock}
    (hd : d.Valid) {p : ZetaGroupedPoint} (hp : p.Valid d) {θ δ : ℝ}
    (hθ : |turingStirlingPhase (p.height d) - θ| ≤ δ)
    (hmargin : p.xiApprox d θ < -p.xiError d δ) : xiCriticalLineValue (p.height d) < 0 := by
  apply (xiCriticalLineValue_neg_iff_normalized _).mpr
  have h := (abs_le.mp (hp.abs_xi_sub_approx_le hd hθ)).2
  linarith

/-- Either orientation of separately evaluated endpoints supplies the actual sign-change row. -/
theorem XiSignRow.valid_of_grouped_endpoints {row : XiSignRow} (hwidth : row.lower < row.upper)
    {d e : ZetaGroupedBlock} (hd : d.Valid) (he : e.Valid)
    {p q : ZetaGroupedPoint} (hp : p.Valid d) (hq : q.Valid e)
    (hlower : p.height d = (row.lower : ℝ)) (hupper : q.height e = (row.upper : ℝ))
    {θ φ δ ε : ℝ} (hθ : |turingStirlingPhase (p.height d) - θ| ≤ δ)
    (hφ : |turingStirlingPhase (q.height e) - φ| ≤ ε)
    (hmargin : (p.xiError d δ < p.xiApprox d θ ∧ q.xiApprox e φ < -q.xiError e ε) ∨
      (p.xiApprox d θ < -p.xiError d δ ∧ q.xiError e ε < q.xiApprox e φ)) : row.Valid := by
  refine ⟨hwidth, ?_⟩
  rw [← hlower, ← hupper]
  rcases hmargin with ⟨hpos, hneg⟩ | ⟨hneg, hpos⟩
  · exact mul_neg_of_pos_of_neg (hp.xi_pos hd hθ hpos) (hq.xi_neg he hφ hneg)
  · exact mul_neg_of_neg_of_pos (hp.xi_neg hd hθ hneg) (hq.xi_pos he hφ hpos)

end

end PrimeFactorUnimodality
