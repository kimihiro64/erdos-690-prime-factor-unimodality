import Mathlib.Tactic.NormNum
import PrimeFactorUnimodality.Mathlib.NumberTheory.LSeries.RiemannZetaEulerIntegral

/-! # Exact interfaces and boundary cases for the complete horizontal tail -/

namespace PrimeFactorUnimodality.Tests

noncomputable section

open Complex Filter MeasureTheory Set
open scoped Topology
open ArithmeticFunction

example (T : ℝ) :
    Tendsto (fun x : ℝ => riemannZetaEulerLog ((x : ℂ) + T * I)) atTop (𝓝 0) := by
  exact tendsto_riemannZetaEulerLog_horizontal_atTop T

example {x : ℝ} (hx : 1 < x) (T : ℝ) :
    HasDerivAt (fun y : ℝ => riemannZetaEulerLog ((y : ℂ) + T * I))
      (logDeriv riemannZeta ((x : ℂ) + T * I)) x := by
  exact hasDerivAt_riemannZetaEulerLog_horizontal hx T

example {σ : ℝ} (hσ : 1 < σ) (T : ℝ) :
    (∫ x in Ioi σ, logDeriv riemannZeta ((x : ℂ) + T * I)) =
      -riemannZetaEulerLog ((σ : ℂ) + T * I) := by
  exact integral_logDeriv_riemannZeta_horizontal_Ioi hσ T

example : Tendsto (fun x : ℝ => riemannZetaEulerLog (x : ℂ)) atTop (𝓝 0) := by
  simpa using tendsto_riemannZetaEulerLog_horizontal_atTop 0

example (T : ℝ) : (∫ x in Ioi (2 : ℝ), logDeriv riemannZeta ((x : ℂ) + (-T) * I)) =
    -riemannZetaEulerLog ((2 : ℂ) + (-T) * I) := by
  simpa using integral_logDeriv_riemannZeta_horizontal_Ioi (σ := 2) (by norm_num) (-T)

end

end PrimeFactorUnimodality.Tests
