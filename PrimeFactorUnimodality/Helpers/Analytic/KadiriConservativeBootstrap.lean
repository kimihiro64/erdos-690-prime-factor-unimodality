import PrimeFactorUnimodality.Helpers.Analytic.KadiriConservativeBudget
import PrimeFactorUnimodality.Helpers.Analytic.KadiriGridBootstrap

/-! # The grid bootstrap with an elementary correction budget

The conservative polynomial has no low-zero mass sum or Euler constant.
Its proved comparison supplies both the actual nonpositive correction and
every grid margin, with the direction justified by the nonnegative grid
index. The low-height zero-location premise remains unchanged.
-/

namespace PrimeFactorUnimodality

noncomputable section

open Real

/-- Elementary endpoint checks imply the actual signed zero-free region on the full height ray. -/
theorem xi_zero_gap_of_conservative_grid_budget
    {θ R r T H η₀ σ₀ δ κ y B₀ B₁ B₂ B₃ : ℝ} {n : ℕ}
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
    (hbudget : kadiriConservativeMomentPolynomial θ η₀ η₀ σ₀ κ δ (-1) H T
      B₀ B₁ B₂ B₃ (1 / r) (Finset.range (n + 1)) a ≤ 0)
    (m : ℕ) (hm : 0 < m) (height : Fin m → ℝ)
    (hheight : ∀ j, 1 < height j)
    (hthreshold : ∀ j, height j ≤ T ∨ height j ≤ exp (1 / (R * (η₀ * ((j : ℝ) + 1) / m))))
    (hmargin : ∀ j, kadiriBootstrapLogCoefficient θ κ (Finset.range (n + 1)) a / r ≤
      min (kadiriTransformGap θ (a 0) (a 1)
        (kadiriBootstrapLowerArgument R r n H (height j)))
        (kadiriTransformGap θ (a 0) (a 1) 1) - ((j : ℝ) / m) *
          kadiriConservativeMomentPolynomial θ η₀ η₀ σ₀ κ δ (-1) H T
            B₀ B₁ B₂ B₃ (1 / r) (Finset.range (n + 1)) a)
    (p : RiemannXiDivisorZeroIndex) (hp : T ≤ |(riemannXiDivisorZeroValue p).im|) :
    1 / (r * log |(riemannXiDivisorZeroValue p).im|) ≤
      1 - (riemannXiDivisorZeroValue p).re := by
  have hη₀ : 0 < η₀ := by
    rw [hηdef]
    exact one_div_pos.mpr (mul_pos hr (log_pos (by linarith)))
  have hM : 0 ≤ kadiriMomentMassBound (-1) B₀ B₁ B₂ B₃ :=
    kadiriMomentMassBound_nonneg (by norm_num)
      ((kadiriDerivativeMoment_nonneg hθ 0).trans hB₀)
      ((kadiriDerivativeMoment_nonneg hθ 1).trans hB₁)
      ((kadiriDerivativeMoment_nonneg hθ 2).trans hB₂)
      ((kadiriDerivativeMoment_nonneg hθ 3).trans hB₃)
  have hcomparison := kadiriMomentCorrectionPolynomial_le_conservative
    (η₀ := η₀) (δ := δ) (H := H) (T := T) (q := 1 / r)
    hθ hη₀.le hσ₀ hκ hM (Finset.range (n + 1)) a ha₀.le
  refine xi_zero_gap_of_grid_moment_budget hR hr hT hH hn hθ hηdef hηhalf
    hσdef hσ₀ hδ hκ hκ₁ hκ₂ hκ₃ hc hgap hcut hy hdy hend hB₀ hB₁ hB₂ hB₃
    a ha ha₀ ha₁ hpoly hlow hhigh (hcomparison.trans hbudget)
    m hm height hheight hthreshold ?_ p hp
  intro j
  exact (hmargin j).trans (sub_le_sub_left
    (mul_le_mul_of_nonneg_left hcomparison
      (div_nonneg (Nat.cast_nonneg j.val) (Nat.cast_nonneg m))) _)

end

end PrimeFactorUnimodality
