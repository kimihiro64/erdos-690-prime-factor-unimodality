import PrimeFactorUnimodality.Helpers.Analytic.KadiriDistinguishedZero

/-! # Distinguished-zero quantitative regressions

The real-axis comparison includes negative arguments and the endpoint
where `σ=β`, so it must not divide by `σ-β`. The degree-16 regression
retains the actual zero at the frequency-one term, with all multiplicities
and the complete outer-strip sum still present.
-/

namespace PrimeFactorUnimodality.Tests

noncomputable section

open Complex Real

example {f : ℝ → ℝ} {d : ℝ} (hd : 0 ≤ d) (hf : ContinuousOn f (Set.Icc 0 d))
    (hf₀ : ∀ u ∈ Set.Icc 0 d, 0 ≤ f u) :
    (finiteLaplace (fun u => (f u : ℂ)) d 0).re ≤
      (finiteLaplace (fun u => (f u : ℂ)) d (-1)).re := by
  simpa using antitone_re_finiteLaplace hd hf hf₀ (show (-1 : ℝ) ≤ 0 by norm_num)

example (θ η η₀ σ₀ κ δ : ℝ) :
    kadiriRetainedPairError θ η η₀ σ₀ κ δ =
      κ * ((1 / δ + 1 / (σ₀ - η₀ + δ)) * kadiriKernel θ 0 * η +
        (1 / δ ^ 3 + 1 / (σ₀ - η₀ + δ) ^ 3) * (-kadiriKernel₂ θ 0) * η ^ 3) -
      (kadiriKernel θ 0 * η - (-kadiriKernel₂ θ 0) * η ^ 3) := by
  unfold kadiriRetainedPairError
  ring

example {θ η η₀ σ₀ σ κ δ : ℝ} (hθ : π / 2 < θ ∧ θ < π) (hη : 0 < η)
    (hσ : σ₀ ≤ σ) (hσ₁ : σ ≤ 1) (hβ₀ : 1 - η₀ ≤ σ)
    (hδ : 0 < δ) (hc : 0 < σ₀ - η₀ + δ) (hκ : 0 ≤ κ) :
    (finiteLaplace (fun u => (kadiriWeight θ η u : ℂ)) (kadiriWeightSupport θ η) 0).re -
        kadiriRetainedPairError θ η η₀ σ₀ κ δ ≤
      smoothedLaplaceDifference (kadiriWeight θ η) (kadiriWeightSupport θ η) κ δ 0 +
        smoothedLaplaceDifference (kadiriWeight θ η) (kadiriWeightSupport θ η) κ δ
          ((2 * σ - 1 : ℝ) : ℂ) := by
  have h := kadiriWeight_retained_pair_lower_bound hθ hη hσ hσ₁ hβ₀ le_rfl hδ hc hκ
  simpa only [sub_self, ofReal_zero, show σ - 1 + σ = 2 * σ - 1 by ring] using h

example {θ η η₀ σ₀ σ δ κ : ℝ}
    (hθ : π / 2 < θ ∧ θ < π) (hη : 0 < η) (hη₀ : η ≤ η₀)
    (hσ₀ : 1 / 2 < σ₀) (hσ : σ₀ ≤ σ) (hσ₁ : σ ≤ 1) (hδ : 0 < δ) (hκ : 0 ≤ κ)
    (hκ₂ : κ ≤ kadiriKappa₂ θ η₀ (2 * σ₀ - 1) δ)
    (hκ₃ : κ ≤ kadiriKappa₃ θ η₀ (2 * σ₀ - 1) δ)
    (hc : 0 < σ₀ - η₀ + δ) (a : ℕ → ℝ) (ha : ∀ i ∈ Finset.range 17, 0 ≤ a i)
    (p : RiemannXiDivisorZeroIndex) (hβ : 1 / 2 < (riemannXiDivisorZeroValue p).re)
    (hβσ : (riemannXiDivisorZeroValue p).re ≤ σ)
    (hηρ : η = 1 - (riemannXiDivisorZeroValue p).re) :
    a 1 * ((finiteLaplace (fun u => (kadiriWeight θ η u : ℂ)) (kadiriWeightSupport θ η)
        ((σ - (riemannXiDivisorZeroValue p).re : ℝ) : ℂ)).re -
      kadiriRetainedPairError θ η η₀ σ₀ κ δ) +
      (∑ i ∈ Finset.range 17, a i * ∑' q : {q : RiemannXiDivisorZeroIndex //
          ¬ kadiriCentralStrip σ (riemannXiDivisorZeroValue q)},
        smoothedLaplaceDifference (kadiriWeight θ η) (kadiriWeightSupport θ η) κ δ
          (((σ : ℂ) + ((i : ℝ) * (riemannXiDivisorZeroValue p).im : ℝ) * I) -
            riemannXiDivisorZeroValue q.1)) ≤
      ∑ i ∈ Finset.range 17, a i * ∑' q : RiemannXiDivisorZeroIndex,
        smoothedLaplaceDifference (kadiriWeight θ η) (kadiriWeightSupport θ η) κ δ
          (((σ : ℂ) + ((i : ℝ) * (riemannXiDivisorZeroValue p).im : ℝ) * I) -
            riemannXiDivisorZeroValue q) :=
  kadiriWeight_distinguished_zero_sum_lower_bound hθ hη hη₀ hσ₀ hσ hσ₁ hδ hκ hκ₂ hκ₃ hc
    (Finset.range 17) a (fun i : ℕ => (i : ℝ)) ha 1 (by decide) (by norm_num) p hβ hβσ hηρ

end

end PrimeFactorUnimodality.Tests
