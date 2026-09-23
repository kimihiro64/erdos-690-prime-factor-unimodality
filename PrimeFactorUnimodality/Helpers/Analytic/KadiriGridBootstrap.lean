import Mathlib.Order.SuccPred.IntervalSucc
import PrimeFactorUnimodality.Helpers.Analytic.KadiriScaleCoverBootstrap

/-! # Uniform scale grids for the zero-free bootstrap

Mathlib's monotone adjacent-interval union theorem covers every scale in
`(0,eta0]`, including grid endpoints, with no enumeration of real inputs.
Only the chosen height and numerical margin for each grid interval remain.
The correction multiplier simplifies exactly to the rational index `j/m`.
-/

namespace PrimeFactorUnimodality

noncomputable section

open Real

/-- Any positive number of uniform scale bands suffices when its endpoint budgets hold. -/
theorem xi_zero_gap_of_grid_moment_budget
    {θ R r T H η₀ σ₀ δ κ y B₀ B₁ B₂ B₃ : ℝ} {n : ℕ}
    (hR : 0 < R) (hr : 0 < r) (hT : 10 ≤ T) (hH : 4 ≤ H) (hn : 1 ≤ n)
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
    (hbudget : kadiriMomentCorrectionPolynomial θ η₀ η₀ σ₀ κ δ (-1) H T
      B₀ B₁ B₂ B₃ (1 / r) (Finset.range (n + 1)) a ≤ 0)
    (m : ℕ) (hm : 0 < m) (height : Fin m → ℝ)
    (hheight : ∀ j, 1 < height j)
    (hthreshold : ∀ j, height j ≤ T ∨ height j ≤ exp (1 / (R * (η₀ * ((j : ℝ) + 1) / m))))
    (hmargin : ∀ j, kadiriBootstrapLogCoefficient θ κ (Finset.range (n + 1)) a / r ≤
      min (kadiriTransformGap θ (a 0) (a 1)
        (kadiriBootstrapLowerArgument R r n H (height j)))
        (kadiriTransformGap θ (a 0) (a 1) 1) - ((j : ℝ) / m) *
          kadiriMomentCorrectionPolynomial θ η₀ η₀ σ₀ κ δ (-1) H T
            B₀ B₁ B₂ B₃ (1 / r) (Finset.range (n + 1)) a)
    (p : RiemannXiDivisorZeroIndex) (hp : T ≤ |(riemannXiDivisorZeroValue p).im|) :
    1 / (r * log |(riemannXiDivisorZeroValue p).im|) ≤
      1 - (riemannXiDivisorZeroValue p).re := by
  have hη₀ : 0 < η₀ := by
    rw [hηdef]
    exact one_div_pos.mpr (mul_pos hr (log_pos (by linarith)))
  have hmpos : (0 : ℝ) < m := Nat.cast_pos.mpr hm
  refine xi_zero_gap_of_scale_cover_moment_budget hR hr hT hH hn hθ hηdef hηhalf
    hσdef hσ₀ hδ hκ hκ₁ hκ₂ hκ₃ hc hgap hcut hy hdy hend hB₀ hB₁ hB₂ hB₃
    a ha ha₀ ha₁ hpoly hlow hhigh hbudget
    (fun j : Fin m => η₀ * (j : ℝ) / m)
    (fun j : Fin m => η₀ * ((j : ℝ) + 1) / m) height ?_ hheight hthreshold ?_ p hp
  · intro η hη hscale
    have hmono : Monotone (fun j : ℕ => η₀ * (j : ℝ) / m) := by
      intro i j hij
      exact div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left (Nat.cast_le.mpr hij) hη₀.le) hmpos.le
    have hmem : η ∈ Set.Ioc (η₀ * (0 : ℕ) / m) (η₀ * (m : ℕ) / m) := by
      simpa only [Nat.cast_zero, mul_zero, zero_div, mul_div_cancel_right₀ _ hmpos.ne']
        using (show η ∈ Set.Ioc 0 η₀ from ⟨hη, hscale⟩)
    rw [← hmono.biUnion_Ico_Ioc_map_succ 0 m] at hmem
    obtain ⟨j, hj, hjη⟩ := Set.mem_iUnion₂.mp hmem
    refine ⟨⟨j, hj.2⟩, hjη.1.le, ?_⟩
    simpa only [Order.succ_eq_add_one, Nat.cast_add, Nat.cast_one] using hjη.2
  · intro j
    have he : (η₀ * (j : ℝ) / m) / η₀ = (j : ℝ) / m := by
      field_simp
    simpa only [he] using hmargin j

end

end PrimeFactorUnimodality
