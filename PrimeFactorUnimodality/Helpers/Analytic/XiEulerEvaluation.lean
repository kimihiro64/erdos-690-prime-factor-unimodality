import PrimeFactorUnimodality.Helpers.Analytic.XiStirlingPhase
import PrimeFactorUnimodality.Helpers.Analytic.ZetaEulerApproximation

/-! # Higher-order finite evaluation and sign bounds for actual xi values

The arbitrary-order Euler approximation and the complete shifted-Gamma
phase error give an explicit normalized interval at any real height.
Strict interval margins imply actual xi signs. Evaluation of the remaining
elementary finite expressions is a separate obligation, not assumed here.
-/

namespace PrimeFactorUnimodality

noncomputable section

open Complex

/-- Finite normalized approximation, without xi's exponentially small positive amplitude. -/
def xiEulerApprox (N m : ℕ) (t : ℝ) : ℝ :=
  (exp (I * turingStirlingPhase t) *
    zetaEulerApproxOrder N ((1 / 2 : ℂ) + t * I) m).re

/-- Complete analytic error before additional rounding or elementary-function errors. -/
def xiEulerError (N m : ℕ) (t : ℝ) : ℝ :=
  zetaEulerError N ((1 / 2 : ℂ) + t * I) m +
    ‖zetaEulerApproxOrder N ((1 / 2 : ℂ) + t * I) m‖ / 10

/-- The finite formula encloses normalized xi for every real height and every order. -/
theorem abs_xiNormalizedValue_sub_eulerApprox_le {N : ℕ} (hN : 0 < N)
    (m : ℕ) (t : ℝ) :
    |xiNormalizedValue t - xiEulerApprox N m t| ≤ xiEulerError N m t := by
  apply abs_xiNormalizedValue_sub_stirlingApprox_le
  exact norm_riemannZeta_sub_eulerApproxOrder_le hN (by norm_num)
    (by intro he; have hr := congrArg Complex.re he; norm_num at hr) m

/-- Finite evaluation errors are added to both analytic remainders before taking signs. -/
theorem abs_xiNormalizedValue_sub_roundedEuler_le {N : ℕ} (hN : 0 < N)
    (m : ℕ) {t θ ε δ : ℝ} {w : ℂ}
    (hw : ‖zetaEulerApproxOrder N ((1 / 2 : ℂ) + t * I) m - w‖ ≤ ε)
    (hθ : |turingStirlingPhase t - θ| ≤ δ) :
    |xiNormalizedValue t - (exp (I * θ) * w).re| ≤
      zetaEulerError N ((1 / 2 : ℂ) + t * I) m + ε + ‖w‖ * (1 / 10 + δ) := by
  apply abs_xiNormalizedValue_sub_approx_le
  · exact (norm_sub_le_norm_sub_add_norm_sub _ _ _).trans
      (add_le_add (norm_riemannZeta_sub_eulerApproxOrder_le hN (by norm_num)
        (by intro he; have hr := congrArg Complex.re he; norm_num at hr) m) hw)
  · exact (abs_sub_le _ _ _).trans
      (add_le_add (abs_turingCountingPhase_sub_stirling_le t) hθ)

/-- A positive lower endpoint proves positivity of the actual xi function. -/
theorem xiCriticalLineValue_pos_of_eulerApprox {N m : ℕ} (hN : 0 < N) {t : ℝ}
    (hmargin : xiEulerError N m t < xiEulerApprox N m t) :
    0 < xiCriticalLineValue t := by
  apply (xiCriticalLineValue_pos_iff_normalized t).mpr
  have h := (abs_le.mp (abs_xiNormalizedValue_sub_eulerApprox_le hN m t)).1
  linarith

/-- A negative upper endpoint proves negativity of the actual xi function. -/
theorem xiCriticalLineValue_neg_of_eulerApprox {N m : ℕ} (hN : 0 < N) {t : ℝ}
    (hmargin : xiEulerApprox N m t < -xiEulerError N m t) :
    xiCriticalLineValue t < 0 := by
  apply (xiCriticalLineValue_neg_iff_normalized t).mpr
  have h := (abs_le.mp (abs_xiNormalizedValue_sub_eulerApprox_le hN m t)).2
  linarith

/-- Either orientation of separated intervals supplies the sign-change verifier's premise. -/
theorem xiCriticalLineValue_mul_neg_of_eulerApprox {N M k m : ℕ}
    (hN : 0 < N) (hM : 0 < M) {a b : ℝ}
    (hmargin :
      (xiEulerError N k a < xiEulerApprox N k a ∧
        xiEulerApprox M m b < -xiEulerError M m b) ∨
      (xiEulerApprox N k a < -xiEulerError N k a ∧
        xiEulerError M m b < xiEulerApprox M m b)) :
    xiCriticalLineValue a * xiCriticalLineValue b < 0 := by
  rcases hmargin with ⟨ha, hb⟩ | ⟨ha, hb⟩
  · exact mul_neg_of_pos_of_neg (xiCriticalLineValue_pos_of_eulerApprox hN ha)
      (xiCriticalLineValue_neg_of_eulerApprox hM hb)
  · exact mul_neg_of_neg_of_pos (xiCriticalLineValue_neg_of_eulerApprox hN ha)
      (xiCriticalLineValue_pos_of_eulerApprox hM hb)

end

end PrimeFactorUnimodality
