import PrimeFactorUnimodality.Helpers.Analytic.KadiriLaplacePositivity

/-! # Real transform positivity, including the imaginary axis

The regressions keep every admissible angle, positive scale, and point of
the closed right half-plane. Generic tests also allow sign-changing source
functions and retain the exact Volterra energy identity.
-/

namespace PrimeFactorUnimodality.Tests

noncomputable section

open Complex

example {F : ℝ × ℝ → ℂ} (hF : Continuous F) {a b : ℝ} (hab : a ≤ b) :
    (∫ u in (0 : ℝ)..b - a, ∫ v in a..b - u, F (u, v)) =
      ∫ v in a..b, ∫ u in (0 : ℝ)..b - v, F (u, v) :=
  intervalIntegral.integral_integral_triangle_swap hF hab

example {q : ℝ → ℝ} (hq : Continuous q) {a b : ℝ} (hab : a ≤ b) (s : ℂ) :
    (finiteLaplace (fun u => ((∫ v in a..b - u, q v * q (v + u) : ℝ) : ℂ)) (b - a) s).re =
      ‖finiteVolterra q b (-s) a‖ ^ 2 / 2 +
        s.re * ∫ v in a..b, ‖finiteVolterra q b (-s) v‖ ^ 2 :=
  re_finiteLaplace_correlation_eq_energy hq hab s

example (s : ℂ) (hs : 0 ≤ s.re) :
    0 ≤ (finiteLaplace (fun u => ((∫ v in (-1 : ℝ)..1 - u, v * (v + u) : ℝ) : ℂ)) 2 s).re := by
  convert re_finiteLaplace_correlation_nonneg (q := fun v => v) continuous_id
    (a := -1) (b := 1) (by norm_num) hs using 1
  norm_num

example (s : ℂ) (hs : 0 < s.re) :
    0 < (finiteLaplace (fun u => ((∫ v in (-1 : ℝ)..1 - u, v * (v + u) : ℝ) : ℂ)) 2 s).re := by
  convert re_finiteLaplace_correlation_pos (q := fun v => v) continuous_id
    (a := -1) (b := 1) ⟨1 / 2, by norm_num, by norm_num⟩ hs using 1
  norm_num

example {θ η : ℝ} (hθ : Real.pi / 2 < θ ∧ θ < Real.pi) (hη : 0 < η)
    (s : ℂ) (hs : 0 ≤ s.re) :
    0 ≤ (finiteLaplace (fun u => (kadiriWeight θ η u : ℂ)) (kadiriWeightSupport θ η) s).re :=
  re_kadiriWeight_laplace_nonneg hθ hη hs

example {θ η : ℝ} (hθ : Real.pi / 2 < θ ∧ θ < Real.pi) (hη : 0 < η)
    (s : ℂ) (hs : 0 < s.re) :
    0 < (finiteLaplace (fun u => (kadiriWeight θ η u : ℂ)) (kadiriWeightSupport θ η) s).re :=
  re_kadiriWeight_laplace_pos hθ hη hs

example {η : ℝ} (hη : 0 < η) (y : ℝ) :
    0 ≤ (finiteLaplace (fun u => (kadiriWeight (185573 / 100000) η u : ℂ))
      (kadiriWeightSupport (185573 / 100000) η) ((y : ℂ) * I)).re :=
  re_kadiriWeight_laplace_nonneg mossinghoffTrudgian_theta_mem hη (by simp)

example (f : ℝ → ℂ) (d : ℝ) (s : ℂ) :
    finiteLaplace (fun u => (-2 : ℂ) * f (-2 * u)) (d / -2) s =
      finiteLaplace f d (s / -2) := by
  simpa using finiteLaplace_rescale f d s (η := -2) (by norm_num)

end

end PrimeFactorUnimodality.Tests
