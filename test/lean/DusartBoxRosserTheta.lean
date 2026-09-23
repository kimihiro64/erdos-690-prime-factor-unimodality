import PrimeFactorUnimodality.Helpers.Analytic.DusartBoxRosserTheta

/-! # Regression tests for complete Rosser cutoff selection -/

namespace PrimeFactorUnimodality.Tests

open Chebyshev Real

example {x ε : ℝ} (hx : 0 < x)
    (hpsi : |ψ x - x| / x ≤ ε)
    (hupper : ε < 1 / 36260)
    (hlower : ε + dusartThetaRootRelativeCorrection x < (12323 / 10000 : ℝ) / Real.log x) :
    θ x - x < x / 36260 ∧
      |θ x - x| < (12323 / 10000 : ℝ) * x / Real.log x :=
  dusartTheta_margins_of_normalized_psi hx hpsi hupper hlower

example {X R a H δ : ℝ} {ε : ℝ → ℝ}
    (hX : 3 ≤ X) (hR : 0 < R) (ha : 10 ≤ a) (haH : a < H) (hH : 10 ^ 9 ≤ H) (hδ : 0 < δ)
    (finite : HasDusartSymmetricThetaBoundsBelow X)
    (hgap : ∀ z ∈ xiLowHeightIndices H, (riemannXiDivisorZeroValue z).re ≤ 1 - δ)
    (hreg : ∀ z : RiemannXiDivisorZeroIndex, H ≤ |(riemannXiDivisorZeroValue z).im| →
      (riemannXiDivisorZeroValue z).re ≤
        1 - 1 / (R * Real.log |(riemannXiDivisorZeroValue z).im|))
    (hscalar : ∀ x : ℝ, X ≤ x → ∃ (m : ℕ) (s ν : ℝ),
      0 < s ∧ 1 < x * (1 - (m + 3 : ℕ) * s) ∧
      0 < ν ∧ ν ≤ 1 ∧ 1 < (m + 3 : ℕ) * ν ^ 2 ∧
      max ((1 - (m + 3 : ℕ) * s) *
        dusartBoxRosserMixedBudget m (s / (1 - (m + 3 : ℕ) * s))
          (x * (1 - (m + 3 : ℕ) * s)) R ν a H δ)
        (dusartBoxRosserMixedBudget m s x R ν a H δ) + (m + 3 : ℕ) * s / 2 ≤ ε x)
    (hupper : ∀ x : ℝ, X ≤ x → ε x < 1 / 36260)
    (hlower : ∀ x : ℝ, X ≤ x →
      ε x + dusartThetaRootRelativeCorrection x < (12323 / 10000 : ℝ) / Real.log x) :
    HasDusartThetaBounds :=
  hasDusartThetaBounds_of_rosserMixed hX hR ha haH hH hδ finite hgap hreg hscalar hupper hlower

end PrimeFactorUnimodality.Tests
