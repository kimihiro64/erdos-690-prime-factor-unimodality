import PrimeFactorUnimodality.Mathlib.Analysis.Fourier.ExponentialAliasing
import PrimeFactorUnimodality.Mathlib.Analysis.Fourier.Scaling
import PrimeFactorUnimodality.Mathlib.Analysis.SpecialFunctions.Gaussian.RapidDecay

/-! Exact geometric tails, signed scaling and two-sided rapid decay. -/

open scoped FourierTransform

example {a A u : ℝ} (ha : 0 < a) (hA : 0 < A) (hu : |u| ≤ A / 2) :
    ‖(∑' n : ℤ, Real.exp (-a * |u + (n : ℝ) * A|)) - Real.exp (-a * |u|)‖ ≤
      2 * Real.exp (-a * A / 2) / (1 - Real.exp (-a * A)) := by
  simpa only [Finset.sum_singleton, one_mul, mul_div_assoc] using
    Fourier.norm_periodization_sub_le_of_finite_exp_bound (s := {(0 : ℕ)})
      (c := fun _ => 1) (a := fun _ => a) (f := fun x => Real.exp (-a * |x|))
      (fun _ _ => by norm_num) (fun _ _ => ha) hA hu (fun v => by simp)

example (f : ℝ → ℂ) (u : ℝ) :
    𝓕 (fun x : ℝ => f (-2 * x)) u = (1 / 2 : ℝ) • 𝓕 f (u / -2) := by
  simpa using Real.fourier_comp_mul_left f (B := -2) (by norm_num) u

example (k : ℕ) {b : ℝ} (hb : 0 < b) :
    Asymptotics.IsLittleO (Filter.cocompact ℝ)
      (fun x : ℝ => |x| ^ k * Real.exp (-b * x ^ 2)) (fun x : ℝ => |x| ^ (-(2 : ℝ))) :=
  Real.abs_pow_mul_exp_neg_mul_sq_isLittleO_cocompact k hb (-2)
