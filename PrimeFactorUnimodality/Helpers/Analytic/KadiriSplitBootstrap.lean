import PrimeFactorUnimodality.Helpers.Analytic.KadiriScaleCoverBootstrap

/-! # The two-scale actual zero-free-region bootstrap

For small actual zero gaps the prior region forces a higher ordinate, which
improves the transform interval. For larger gaps the band estimate retains
a fixed negative correction. Single-crossing endpoint minima preserve
the cancellation in both transform bounds. All numerical endpoint inputs
and low-height information remain explicit obligations.
-/

namespace PrimeFactorUnimodality

noncomputable section

open Real

/-- Two fixed scale regimes improve the actual region at every positive or negative ordinate. -/
theorem xi_zero_gap_of_split_moment_budget
    {θ R r T T₁ H η₀ η₁ σ₀ δ κ y B₀ B₁ B₂ B₃ : ℝ} {n : ℕ}
    (hR : 0 < R) (hr : 0 < r) (hT : 10 ≤ T) (hH : 4 ≤ H) (hn : 1 ≤ n)
    (hθ : π / 2 < θ ∧ θ < π)
    (hηdef : η₀ = 1 / (r * log T)) (hηhalf : η₀ ≤ 1 / 2)
    (_hη₁ : 0 < η₁) (hT₁ : 1 < T₁) (hthreshold : T₁ ≤ exp (1 / (R * η₁)))
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
    (hB₀ : kadiriDerivativeMoment θ 0 ≤ B₀) (hB₁ : kadiriDerivativeMoment θ 1 ≤ B₁)
    (hB₂ : kadiriDerivativeMoment θ 2 ≤ B₂) (hB₃ : kadiriDerivativeMoment θ 3 ≤ B₃)
    (a : ℕ → ℝ) (ha : ∀ i ∈ Finset.range (n + 1), 0 ≤ a i)
    (ha₀ : 0 < a 0) (ha₁ : 0 < a 1)
    (hpoly : ∀ u : ℝ, 0 ≤ ∑ i ∈ Finset.range (n + 1), a i * Real.cos ((i : ℝ) * u))
    (hlow : ∀ p : RiemannXiDivisorZeroIndex,
      |(riemannXiDivisorZeroValue p).im| < T → (riemannXiDivisorZeroValue p).re ≤ σ₀)
    (hhigh : ∀ p : RiemannXiDivisorZeroIndex,
      T ≤ |(riemannXiDivisorZeroValue p).im| →
        1 / (R * log |(riemannXiDivisorZeroValue p).im|) ≤
          1 - (riemannXiDivisorZeroValue p).re)
    (hbudget : kadiriMomentCorrectionPolynomial θ η₀ η₀ σ₀ κ δ (-1) H T
      B₀ B₁ B₂ B₃ (1 / r) (Finset.range (n + 1)) a ≤ 0)
    (hsmallMargin : kadiriBootstrapLogCoefficient θ κ (Finset.range (n + 1)) a / r ≤
      min (kadiriTransformGap θ (a 0) (a 1) (kadiriBootstrapLowerArgument R r n H T₁))
        (kadiriTransformGap θ (a 0) (a 1) 1))
    (hlargeMargin : kadiriBootstrapLogCoefficient θ κ (Finset.range (n + 1)) a / r ≤
      min (kadiriTransformGap θ (a 0) (a 1) (kadiriBootstrapLowerArgument R r n H T))
        (kadiriTransformGap θ (a 0) (a 1) 1) - (η₁ / η₀) *
          kadiriMomentCorrectionPolynomial θ η₀ η₀ σ₀ κ δ (-1) H T
            B₀ B₁ B₂ B₃ (1 / r) (Finset.range (n + 1)) a)
    (p : RiemannXiDivisorZeroIndex) (hp : T ≤ |(riemannXiDivisorZeroValue p).im|) :
    1 / (r * log |(riemannXiDivisorZeroValue p).im|) ≤
      1 - (riemannXiDivisorZeroValue p).re := by
  refine xi_zero_gap_of_scale_cover_moment_budget hR hr hT hH hn hθ hηdef hηhalf
    hσdef hσ₀ hδ hκ hκ₁ hκ₂ hκ₃ hc hgap hcut hy hdy hend hB₀ hB₁ hB₂ hB₃
    a ha ha₀ ha₁ hpoly hlow hhigh hbudget
    (fun b : Bool => if b then η₁ else 0)
    (fun b : Bool => if b then η₀ else η₁)
    (fun b : Bool => if b then T else T₁) ?_ ?_ ?_ ?_ p hp
  · intro η hη hscale
    by_cases hsmall : η ≤ η₁
    · exact ⟨false, hη.le, hsmall⟩
    · exact ⟨true, (lt_of_not_ge hsmall).le, hscale⟩
  · intro b
    cases b
    · exact hT₁
    · dsimp
      linarith
  · intro b
    cases b
    · exact Or.inr hthreshold
    · exact Or.inl le_rfl
  · intro b
    cases b
    · simpa using hsmallMargin
    · simpa using hlargeMargin

end

end PrimeFactorUnimodality
