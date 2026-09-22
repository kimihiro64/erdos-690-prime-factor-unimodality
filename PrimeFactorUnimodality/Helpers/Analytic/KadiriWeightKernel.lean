import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Tactic.Ring

/-! # The trigonometric smoothing kernel used by Kadiri and Mossinghoff--Trudgian

These are the actual parameterized kernel and its first two derivatives,
before restricting to its support or applying the scale `eta`. The formula
is that of Kadiri section 2.2 and Mossinghoff--Trudgian section 2; the latter
uses `theta = 1.85573`. Derivative identities require no numerical replay.

Sources: <https://www.cs.uleth.ca/~kadiri/articles/zeta-acta-04-09-07.pdf>
and <https://arxiv.org/abs/1410.3926>.
-/

namespace PrimeFactorUnimodality

noncomputable section

open Real

/-- The unscaled support length of the paper's compact smoothing function. -/
def kadiriSupport (θ : ℝ) : ℝ := -2 * θ / tan θ

/-- The unscaled kernel, written with the support length to expose endpoint cancellation. -/
def kadiriKernel (θ u : ℝ) : ℝ :=
  (1 + tan θ ^ 2) *
    ((1 + tan θ ^ 2) * ((kadiriSupport θ - u) / 2) * cos (u * tan θ) +
      kadiriSupport θ - u - sin (2 * θ + u * tan θ) / sin (2 * θ) +
      2 * (1 + sin (θ + u * tan θ) / sin θ))

/-- The first derivative of the unscaled kernel on its support. -/
def kadiriKernel₁ (θ u : ℝ) : ℝ :=
  (1 + tan θ ^ 2) *
    ((1 + tan θ ^ 2) *
        (-(1 / 2 : ℝ) * cos (u * tan θ) -
          ((kadiriSupport θ - u) / 2) * tan θ * sin (u * tan θ)) -
      1 - tan θ * cos (2 * θ + u * tan θ) / sin (2 * θ) +
      2 * tan θ * cos (θ + u * tan θ) / sin θ)

/-- The second derivative of the unscaled kernel on its support. -/
def kadiriKernel₂ (θ u : ℝ) : ℝ :=
  (1 + tan θ ^ 2) *
    ((1 + tan θ ^ 2) *
        (tan θ * sin (u * tan θ) -
          ((kadiriSupport θ - u) / 2) * tan θ ^ 2 * cos (u * tan θ)) +
      tan θ ^ 2 * sin (2 * θ + u * tan θ) / sin (2 * θ) -
      2 * tan θ ^ 2 * sin (θ + u * tan θ) / sin θ)

/-- Direct differentiation gives the paper's first kernel derivative. -/
theorem hasDerivAt_kadiriKernel (θ u : ℝ) :
    HasDerivAt (kadiriKernel θ) (kadiriKernel₁ θ u) u := by
  have hp := (hasDerivAt_id u).mul_const (tan θ)
  have h2 := hp.const_add (2 * θ)
  have h1 := hp.const_add θ
  have hl := ((hasDerivAt_const u (kadiriSupport θ)).sub (hasDerivAt_id u)).div_const 2
  have h := (((((hl.const_mul (1 + tan θ ^ 2)).mul hp.cos).add_const (kadiriSupport θ)).sub
    (hasDerivAt_id u)).sub (h2.sin.div_const (sin (2 * θ)))).add
      (((h1.sin.div_const (sin θ)).const_add 1).const_mul 2)
  convert h.const_mul (1 + tan θ ^ 2) using 1
  · funext x
    dsimp [kadiriKernel]
  · dsimp [kadiriKernel₁]
    ring

/-- A second differentiation gives the kernel used in the explicit-formula remainder. -/
theorem hasDerivAt_kadiriKernel₁ (θ u : ℝ) :
    HasDerivAt (kadiriKernel₁ θ) (kadiriKernel₂ θ u) u := by
  have hp := (hasDerivAt_id u).mul_const (tan θ)
  have h2 := hp.const_add (2 * θ)
  have h1 := hp.const_add θ
  have hl := ((hasDerivAt_const u (kadiriSupport θ)).sub (hasDerivAt_id u)).div_const 2
  have hinner := (hp.cos.const_mul (-(1 / 2 : ℝ))).sub ((hl.mul_const (tan θ)).mul hp.sin)
  have h := (((hinner.const_mul (1 + tan θ ^ 2)).sub_const 1).sub
    ((h2.cos.const_mul (tan θ)).div_const (sin (2 * θ)))).add
      ((h1.cos.const_mul (2 * tan θ)).div_const (sin θ))
  convert h.const_mul (1 + tan θ ^ 2) using 1
  · funext x
    dsimp [kadiriKernel₁]
  · dsimp [kadiriKernel₂]
    ring

/-- The raw kernel is continuous even before restricting to its compact support. -/
theorem continuous_kadiriKernel (θ : ℝ) : Continuous (kadiriKernel θ) := by
  unfold kadiriKernel
  fun_prop

/-- The raw first derivative is continuous. -/
theorem continuous_kadiriKernel₁ (θ : ℝ) : Continuous (kadiriKernel₁ θ) := by
  unfold kadiriKernel₁
  fun_prop

/-- The raw second derivative is continuous. -/
theorem continuous_kadiriKernel₂ (θ : ℝ) : Continuous (kadiriKernel₂ θ) := by
  unfold kadiriKernel₂
  fun_prop

end

end PrimeFactorUnimodality
