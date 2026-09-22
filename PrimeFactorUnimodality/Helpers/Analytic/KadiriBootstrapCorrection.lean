import PrimeFactorUnimodality.Helpers.Analytic.KadiriBootstrapBudget
import PrimeFactorUnimodality.Helpers.Analytic.KadiriGammaBudget

/-! # Leading coefficient and explicit cubic-scale correction

Expand the complete budget, keeping its signed linear term, exact
derivative mass, and closed-tail majorant. For fixed remaining parameters
the correction is cubic in the scale. This is an exact normalization of
the currently proved bounds, not a claim that their numerical constants
already give the target zero-free region.
-/

namespace PrimeFactorUnimodality

noncomputable section

open Real

/-- The coefficient of `eta*log(t)`, with the zero harmonic omitted. -/
def kadiriBootstrapLogCoefficient (θ κ : ℝ) (S : Finset ℕ) (a : ℕ → ℝ) : ℝ :=
  kadiriKernel θ 0 * (1 - κ) / 2 * (∑ i ∈ S.erase 0, a i)

/-- All remaining terms, including the signed retained-pair contribution. -/
def kadiriBootstrapCorrection (θ η η₀ σ₀ σ κ δ z H t : ℝ)
    (S : Finset ℕ) (a : ℕ → ℝ) : ℝ :=
  η * kadiriKernel θ 0 *
    (a 1 * (κ * (1 / δ + 1 / (σ₀ - η₀ + δ)) - 1) + kadiriGammaResidual κ σ t S a) +
  η ^ 2 * kadiriDerivativeMass θ z *
    (kadiriPoleCoefficient S a t +
      (∑ i ∈ S, a i * xiLehmanTailMajorant ((i : ℝ) * t) H) / 2) +
  η ^ 3 * (-kadiriKernel₂ θ 0) *
    (a 1 * (1 + κ * (1 / δ ^ 3 + 1 / (σ₀ - η₀ + δ) ^ 3)) +
      (1 + 2 * κ) * (∑ i ∈ S, a i * xiLehmanTailMajorant ((i : ℝ) * t) H) /
        (2 * (σ₀ - 1 / 2)) + (∑ i ∈ S, a i) * (1 + κ) / 4)

/-- The original complete budget is exactly its leading logarithm plus the correction. -/
theorem kadiriBootstrapBudget_eq_log_add_correction {θ η η₀ σ₀ σ κ δ z H t : ℝ}
    (hθ : π / 2 < θ ∧ θ < π) (hη : 0 < η) (ht : 0 < t)
    (S : Finset ℕ) (h₀ : 0 ∈ S) (a : ℕ → ℝ) :
    kadiriBootstrapBudget θ η η₀ σ₀ σ κ δ z H t S a =
      kadiriBootstrapLogCoefficient θ κ S a * η * Real.log t +
      kadiriBootstrapCorrection θ η η₀ σ₀ σ κ δ z H t S a := by
  have hw : kadiriWeight θ η 0 = η * kadiriKernel θ 0 := by
    rw [kadiriWeight_of_mem ⟨le_rfl, (kadiriWeightSupport_pos hθ hη).le⟩, mul_zero]
  unfold kadiriBootstrapBudget
  rw [hw, sum_smoothedGammaFactorMajorant_eq κ σ ht S h₀ a]
  unfold kadiriPoleError kadiriRetainedPairError kadiriOuterError
    kadiriBootstrapLogCoefficient kadiriBootstrapCorrection
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring

/-- A positive distinguished coefficient makes the leading logarithmic coefficient positive. -/
theorem kadiriBootstrapLogCoefficient_pos {θ κ : ℝ}
    (hθ : π / 2 < θ ∧ θ < π) (hκ : κ < 1)
    (S : Finset ℕ) (h₁ : 1 ∈ S) (a : ℕ → ℝ)
    (ha : ∀ i ∈ S, 0 ≤ a i) (ha₁ : 0 < a 1) :
    0 < kadiriBootstrapLogCoefficient θ κ S a := by
  have hs : 0 < ∑ i ∈ S.erase 0, a i :=
    Finset.sum_pos' (fun i hi => ha i (Finset.mem_of_mem_erase hi))
      ⟨1, Finset.mem_erase.mpr ⟨by norm_num, h₁⟩, ha₁⟩
  exact mul_pos (div_pos (mul_pos (kadiriKernel_zero_pos hθ) (sub_pos.mpr hκ))
    (by norm_num)) hs

/-- A verified lower margin gives the next numerical region without dividing by a signed error. -/
theorem kadiri_gap_of_bootstrap_margin {θ η η₀ σ₀ σ κ δ z H t R : ℝ}
    (S : Finset ℕ) (a : ℕ → ℝ)
    (hc : 0 < kadiriBootstrapLogCoefficient θ κ S a) (hR : 0 < R) (ht : 1 < t)
    (hmaster : kadiriTransformGap θ (a 0) (a 1) ((1 - σ) / η) ≤
      kadiriBootstrapLogCoefficient θ κ S a * η * Real.log t +
        kadiriBootstrapCorrection θ η η₀ σ₀ σ κ δ z H t S a)
    (hmargin : kadiriBootstrapLogCoefficient θ κ S a / R ≤
      kadiriTransformGap θ (a 0) (a 1) ((1 - σ) / η) -
        kadiriBootstrapCorrection θ η η₀ σ₀ σ κ δ z H t S a) :
    1 / (R * Real.log t) ≤ η := by
  have hm : kadiriBootstrapLogCoefficient θ κ S a * (1 / R) ≤
      kadiriBootstrapLogCoefficient θ κ S a * (η * Real.log t) := by
    simp only [mul_one_div]
    linarith only [hmaster, hmargin]
  have hb := le_of_mul_le_mul_left hm hc
  have hp := (div_le_iff₀ hR).mp hb
  apply (div_le_iff₀ (mul_pos hR (Real.log_pos ht))).mpr
  nlinarith only [hp]

end

end PrimeFactorUnimodality
