import Mathlib.Tactic.NormNum
import PrimeFactorUnimodality.Mathlib.Analysis.SpecialFunctions.Complex.LogNormDeriv

/-! # Exact interfaces and boundary regressions for counting normalization -/

namespace PrimeFactorUnimodality.Tests

noncomputable section

open Complex Filter Set

example {f : ℝ → ℂ} {f' : ℂ} {x : ℝ}
    (hf : HasDerivAt f f' x) (hne : f x ≠ 0) :
    HasDerivAt (fun t => Real.log ‖f t‖) (f' / f x).re x := by
  exact HasDerivAt.log_norm_complex hf hne

example {f : ℂ → ℂ} {f' : ℂ} {x T : ℝ}
    (hf : HasDerivAt f f' ((x : ℂ) + T * I)) (hne : f ((x : ℂ) + T * I) ≠ 0) :
    HasDerivAt (fun y : ℝ => Real.log ‖f ((y : ℂ) + T * I)‖)
      (f' / f ((x : ℂ) + T * I)).re x := by
  exact Complex.HasDerivAt.log_norm_horizontal hf hne

example {f : ℂ → ℂ} {f' : ℂ} {x T : ℝ}
    (hf : HasDerivAt f f' ((x : ℂ) + T * I)) (hne : f ((x : ℂ) + T * I) ≠ 0) :
    HasDerivAt (fun t : ℝ => Real.log ‖f ((x : ℂ) + t * I)‖)
      (-(f' / f ((x : ℂ) + T * I)).im) T := by
  exact Complex.HasDerivAt.log_norm_vertical hf hne

example : HasDerivAt (fun x : ℝ => Real.log ‖(x : ℂ)‖) (-1) (-1) := by
  have h := Complex.HasDerivAt.log_norm_horizontal (x := -1) (T := 0)
    (hasDerivAt_id _) (by norm_num)
  simpa using h

example : HasDerivAt (fun t : ℝ => Real.log ‖(-1 : ℂ) + t * I‖) 0 0 := by
  have h := Complex.HasDerivAt.log_norm_vertical (x := -1) (T := 0)
    (hasDerivAt_id _) (by norm_num)
  simpa using h

example (x : ℝ) : HasDerivAt (fun _ : ℝ => Real.log ‖(-1 : ℂ)‖) 0 x := by
  simpa using (hasDerivAt_const x (-1 : ℂ)).log_norm_complex (by norm_num)

end

end PrimeFactorUnimodality.Tests
