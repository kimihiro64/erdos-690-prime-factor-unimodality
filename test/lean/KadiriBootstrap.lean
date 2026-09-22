import PrimeFactorUnimodality.Helpers.Analytic.KadiriBootstrapMaster

/-! # Exact transform-gap and bootstrap-budget regressions

Check arbitrary degree, the zero-only harmonic set, positive scale,
the normalized strip boundary, and height monotonicity of the Gamma residual.
No numerical bootstrap margin or final zero-free constant is assumed verified.
-/

namespace PrimeFactorUnimodality.Tests

noncomputable section

open Complex Real

example (θ w : ℝ) : kadiriTransformGap θ 0 0 w = 0 := by
  simp [kadiriTransformGap]

example (θ a₀ a₁ w : ℝ) : kadiriTransformGap θ a₀ a₁ w =
    a₁ * (finiteLaplace (fun u => (kadiriKernel θ u : ℂ)) (kadiriSupport θ)
      ((1 - w : ℝ) : ℂ)).re -
    a₀ * (finiteLaplace (fun u => (kadiriKernel θ u : ℂ)) (kadiriSupport θ)
      ((-w : ℝ) : ℂ)).re := kadiriTransformGap_eq_laplace θ a₀ a₁ w

example {θ η σ β : ℝ} (hθ : π / 2 < θ ∧ θ < π) (hη : 0 < η)
    (hηβ : η = 1 - β) (a₀ a₁ : ℝ) :
    a₁ * (finiteLaplace (fun u => (kadiriWeight θ η u : ℂ)) (kadiriWeightSupport θ η)
      ((σ - β : ℝ) : ℂ)).re -
    a₀ * (finiteLaplace (fun u => (kadiriWeight θ η u : ℂ)) (kadiriWeightSupport θ η)
      ((σ - 1 : ℝ) : ℂ)).re = kadiriTransformGap θ a₀ a₁ ((1 - σ) / η) :=
  kadiriWeight_transform_gap_eq hθ hη hηβ a₀ a₁

example {η σ β : ℝ} (hη : 0 < η) (hηβ : η = 1 - β) (hβσ : β ≤ σ) (hσ : σ ≤ 1) :
    (1 - σ) / η ∈ Set.Icc (0 : ℝ) 1 := kadiri_normalized_gap_mem_Icc hη hηβ hβσ hσ

example {η β : ℝ} (hη : 0 < η) (hηβ : η = 1 - β) : (1 - β) / η = 1 := by
  rw [← hηβ, div_self hη.ne']

example (a : ℕ → ℝ) (t : ℝ) : kadiriPoleCoefficient {0} a t = 0 := by
  simp [kadiriPoleCoefficient]

example (θ κ : ℝ) (a : ℕ → ℝ) : kadiriBootstrapLogCoefficient θ κ {0} a = 0 := by
  simp [kadiriBootstrapLogCoefficient]

example {θ η z σ t : ℝ} (ht : t ≠ 0) (n : ℕ) (a : ℕ → ℝ) :
    (∑ i ∈ Finset.range (n + 1), a i * kadiriPoleMajorant θ η z σ ((i : ℝ) * t)) =
      a 0 * (finiteLaplace (fun u => (kadiriWeight θ η u : ℂ))
        (kadiriWeightSupport θ η) ((σ - 1 : ℝ) : ℂ)).re +
      kadiriPoleError θ η z * kadiriPoleCoefficient (Finset.range (n + 1)) a t :=
  sum_kadiriPoleMajorant_nat_eq ht _ (by simp) a

example (κ σ : ℝ) {t : ℝ} (ht : 0 < t) (n : ℕ) (a : ℕ → ℝ) :
    (∑ i ∈ Finset.range (n + 1), a i * smoothedGammaFactorMajorant κ σ ((i : ℝ) * t)) =
      (1 - κ) / 2 * (∑ i ∈ (Finset.range (n + 1)).erase 0, a i) * Real.log t +
        kadiriGammaResidual κ σ t (Finset.range (n + 1)) a :=
  sum_smoothedGammaFactorMajorant_eq κ σ ht _ (by simp) a

example {κ T t : ℝ} (hκ₀ : 0 ≤ κ) (hκ : κ ≤ 1) (σ : ℝ) (S : Finset ℕ) (a : ℕ → ℝ)
    (ha : ∀ i ∈ S, 0 ≤ a i) (hT : 0 < T) (hTt : T ≤ t) :
    kadiriGammaResidual κ σ t S a ≤ kadiriGammaResidual κ σ T S a :=
  antitoneOn_kadiriGammaResidual hκ₀ hκ σ S a ha hT (hT.trans_le hTt) hTt

example {κ σ t : ℝ} (ht : 0 < t) (n : ℕ) (a : ℕ → ℝ)
    (ha : ∀ i ∈ Finset.range (n + 1), 0 ≤ a i) :
    (∑ i ∈ Finset.range (n + 1), a i * smoothedGammaFactorError κ σ ((i : ℝ) * t)) ≤
      a 0 * (κ / (σ + 2)) + (2 * (1 + κ) / t) *
        (∑ i ∈ (Finset.range (n + 1)).erase 0, a i / (i : ℝ)) :=
  sum_smoothedGammaFactorError_le ht _ (by simp) a ha

example (κ σ t : ℝ) (a : ℕ → ℝ) :
    kadiriGammaResidual κ σ t {0} a =
      (1 - κ) / 2 * (a 0 * (Real.log 2 - Real.log π)) + a 0 * (κ / (σ + 2)) := by
  simp [kadiriGammaResidual]

example {θ η η₀ σ₀ σ κ δ z H t : ℝ}
    (hθ : π / 2 < θ ∧ θ < π) (hη : 0 < η) (ht : 0 < t) (n : ℕ) (a : ℕ → ℝ) :
    kadiriBootstrapBudget θ η η₀ σ₀ σ κ δ z H t (Finset.range (n + 1)) a =
      kadiriBootstrapLogCoefficient θ κ (Finset.range (n + 1)) a * η * Real.log t +
      kadiriBootstrapCorrection θ η η₀ σ₀ σ κ δ z H t (Finset.range (n + 1)) a :=
  kadiriBootstrapBudget_eq_log_add_correction hθ hη ht _ (by simp) a

example {θ κ : ℝ} (hθ : π / 2 < θ ∧ θ < π) (hκ : κ < 1)
    (n : ℕ) (hn : 1 ≤ n) (a : ℕ → ℝ)
    (ha : ∀ i ∈ Finset.range (n + 1), 0 ≤ a i) (ha₁ : 0 < a 1) :
    0 < kadiriBootstrapLogCoefficient θ κ (Finset.range (n + 1)) a :=
  kadiriBootstrapLogCoefficient_pos hθ hκ _ (by simp; omega) a ha ha₁

end

end PrimeFactorUnimodality.Tests
