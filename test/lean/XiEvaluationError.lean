import Mathlib.Tactic.NormNum
import PrimeFactorUnimodality.Helpers.Analytic.XiEvaluationError

/-! # Exact interfaces and boundary cases for normalized xi evaluation -/

set_option autoImplicit false

namespace PrimeFactorUnimodality.Tests

noncomputable section

open Complex

example {t θ εζ εθ : ℝ} {w : ℂ}
    (hz : ‖riemannZeta ((1 / 2 : ℂ) + t * I) - w‖ ≤ εζ)
    (hθ : |turingCountingPhase t - θ| ≤ εθ) :
    |xiNormalizedValue t - (exp (I * θ) * w).re| ≤ εζ + ‖w‖ * εθ := by
  exact PrimeFactorUnimodality.abs_xiNormalizedValue_sub_approx_le hz hθ

example {t θ εζ εθ : ℝ} {w : ℂ}
    (hz : ‖riemannZeta ((1 / 2 : ℂ) + t * I) - w‖ ≤ εζ)
    (hθ : |turingCountingPhase t - θ| ≤ εθ)
    (hmargin : εζ + ‖w‖ * εθ < (exp (I * θ) * w).re) :
    0 < xiCriticalLineValue t := by
  exact PrimeFactorUnimodality.xiCriticalLineValue_pos_of_approx hz hθ hmargin

example {t θ εζ εθ : ℝ} {w : ℂ}
    (hz : ‖riemannZeta ((1 / 2 : ℂ) + t * I) - w‖ ≤ εζ)
    (hθ : |turingCountingPhase t - θ| ≤ εθ)
    (hmargin : (exp (I * θ) * w).re < -(εζ + ‖w‖ * εθ)) :
    xiCriticalLineValue t < 0 := by
  exact PrimeFactorUnimodality.xiCriticalLineValue_neg_of_approx hz hθ hmargin

example {a b θa θb εa εb δa δb : ℝ} {u v : ℂ}
    (hab : a < b)
    (ha : ‖riemannZeta ((1 / 2 : ℂ) + a * I) - u‖ ≤ εa)
    (hb : ‖riemannZeta ((1 / 2 : ℂ) + b * I) - v‖ ≤ εb)
    (hθa : |turingCountingPhase a - θa| ≤ δa)
    (hθb : |turingCountingPhase b - θb| ≤ δb)
    (hposa : εa + ‖u‖ * δa < (exp (I * θa) * u).re)
    (hnegb : (exp (I * θb) * v).re < -(εb + ‖v‖ * δb)) :
    ∃ t ∈ Set.Ioo a b, riemannXi ((1 / 2 : ℂ) + t * I) = 0 := by
  exact PrimeFactorUnimodality.exists_xi_zero_of_approx_signs hab ha hb hθa hθb hposa hnegb

example (t : ℝ) :
    |xiNormalizedValue t -
      (exp (I * turingCountingPhase t) * riemannZeta ((1 / 2 : ℂ) + t * I)).re| ≤ 0 := by
  simpa using abs_xiNormalizedValue_sub_approx_le
    (t := t) (θ := turingCountingPhase t) (εζ := 0) (εθ := 0)
    (w := riemannZeta ((1 / 2 : ℂ) + t * I)) (by simp) (by simp)

end

end PrimeFactorUnimodality.Tests
