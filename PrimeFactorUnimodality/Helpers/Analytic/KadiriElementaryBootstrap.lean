import PrimeFactorUnimodality.Helpers.Analytic.KadiriConservativeBootstrap
import PrimeFactorUnimodality.Helpers.Analytic.KadiriElementaryMoments

/-! # An elementary endpoint interface for the actual bootstrap

Substitute the proved derivative-maximum moments into the conservative
grid theorem. All remaining endpoint expressions are elementary real
functions and finite polynomial coefficients: no derivative integral,
low-zero mass sum, or Euler constant needs numerical evaluation here.
The zero-location and previous-region hypotheses remain explicit.
-/

namespace PrimeFactorUnimodality

noncomputable section

open Real

/-- The full correction polynomial after the elementary moment substitution. -/
def kadiriElementaryCorrectionPolynomial (θ η η₀ σ₀ κ δ H T q : ℝ)
    (S : Finset ℕ) (a : ℕ → ℝ) : ℝ :=
  kadiriConservativeMomentPolynomial θ η η₀ σ₀ κ δ (-1) H T
    (kadiriDerivativeMomentElementary θ 0) (kadiriDerivativeMomentElementary θ 1)
    (kadiriDerivativeMomentElementary θ 2) (kadiriDerivativeMomentElementary θ 3) q S a

/-- Elementary numerical margins suffice, with all four moment obligations discharged. -/
theorem xi_zero_gap_of_elementary_grid_budget
    {θ R r T H η₀ σ₀ δ κ y : ℝ} {n : ℕ}
    (hR : 0 < R) (hr : 0 < r) (hT : 10 ^ 9 ≤ T) (hH : 4 ≤ H) (hn : 1 ≤ n)
    (hθ : π / 2 < θ ∧ θ < π)
    (hηdef : η₀ = 1 / (r * log T)) (hηhalf : η₀ ≤ 1 / 2)
    (hσdef : σ₀ = kadiriBootstrapSigma R n H T) (hσ₀ : 1 / 2 < σ₀)
    (hδ : 1 / 2 ≤ δ) (hκ : 0 ≤ κ) (hκ₁ : κ < 1)
    (hκ₂ : κ ≤ kadiriKappa₂ θ η₀ (2 * σ₀ - 1) δ)
    (hκ₃ : κ ≤ kadiriKappa₃ θ η₀ (2 * σ₀ - 1) δ)
    (hc : 0 < σ₀ - η₀ + δ)
    (hgap : 0 ≤ 2 * σ₀ - 1 - κ * (1 + 2 * δ))
    (hcut : κ * (1 + 2 * δ) + 1 - σ₀ ≤
      (2 * σ₀ - 1 - κ * (1 + 2 * δ)) * H ^ 2)
    (hy : 0 < y) (hdy : kadiriSupport θ ≤ y)
    (hend : exp y ≤ 1 + y + y ^ 2 / 2 + y ^ 3 / (345 / 100))
    (a : ℕ → ℝ) (ha : ∀ i ∈ Finset.range (n + 1), 0 ≤ a i)
    (ha₀ : 0 < a 0) (ha₁ : 0 < a 1)
    (hpoly : ∀ u : ℝ, 0 ≤ ∑ i ∈ Finset.range (n + 1), a i * Real.cos ((i : ℝ) * u))
    (hlow : ∀ p : RiemannXiDivisorZeroIndex,
      |(riemannXiDivisorZeroValue p).im| < T → (riemannXiDivisorZeroValue p).re ≤ σ₀)
    (hhigh : ∀ p : RiemannXiDivisorZeroIndex,
      T ≤ |(riemannXiDivisorZeroValue p).im| →
        1 / (R * log |(riemannXiDivisorZeroValue p).im|) ≤
          1 - (riemannXiDivisorZeroValue p).re)
    (hbudget : kadiriElementaryCorrectionPolynomial θ η₀ η₀ σ₀ κ δ H T
      (1 / r) (Finset.range (n + 1)) a ≤ 0)
    (m : ℕ) (hm : 0 < m) (height : Fin m → ℝ)
    (hheight : ∀ j, 1 < height j)
    (hthreshold : ∀ j, height j ≤ T ∨ height j ≤ exp (1 / (R * (η₀ * ((j : ℝ) + 1) / m))))
    (hmargin : ∀ j, kadiriBootstrapLogCoefficient θ κ (Finset.range (n + 1)) a / r ≤
      min (kadiriTransformGap θ (a 0) (a 1)
        (kadiriBootstrapLowerArgument R r n H (height j)))
        (kadiriTransformGap θ (a 0) (a 1) 1) - ((j : ℝ) / m) *
          kadiriElementaryCorrectionPolynomial θ η₀ η₀ σ₀ κ δ H T
            (1 / r) (Finset.range (n + 1)) a)
    (p : RiemannXiDivisorZeroIndex) (hp : T ≤ |(riemannXiDivisorZeroValue p).im|) :
    1 / (r * log |(riemannXiDivisorZeroValue p).im|) ≤
      1 - (riemannXiDivisorZeroValue p).re := by
  exact xi_zero_gap_of_conservative_grid_budget hR hr hT hH hn hθ hηdef hηhalf
    hσdef hσ₀ hδ hκ hκ₁ hκ₂ hκ₃ hc hgap hcut hy hdy hend
    (kadiriDerivativeMoment_le_elementary hθ 0) (kadiriDerivativeMoment_le_elementary hθ 1)
    (kadiriDerivativeMoment_le_elementary hθ 2) (kadiriDerivativeMoment_le_elementary hθ 3)
    a ha ha₀ ha₁ hpoly hlow hhigh hbudget m hm height hheight hthreshold hmargin p hp

end

end PrimeFactorUnimodality
