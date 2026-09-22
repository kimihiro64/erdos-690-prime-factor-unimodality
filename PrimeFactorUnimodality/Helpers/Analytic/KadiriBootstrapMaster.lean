import PrimeFactorUnimodality.Helpers.Analytic.KadiriBootstrapCorrection
import PrimeFactorUnimodality.Helpers.Analytic.KadiriRegionMaster

/-! # The numerical-bootstrap inequality for the actual xi divisor

Combine the established region, actual explicit formula, exact transform
gap, and normalized error budget. The leading coefficient omits the zero
harmonic; its pole has been incorporated into the gap. An explicit margin
then yields an improved zero-free gap. Its numerical verification, the
low-height input, and admissibility checks remain distinct obligations.
-/

namespace PrimeFactorUnimodality

noncomputable section

open Complex Real

variable {θ η η₀ σ₀ σ δ κ z H A R T : ℝ}
    (hR : 0 < R) (hT : 1 < T)
    (hθ : π / 2 < θ ∧ θ < π) (hη : 0 < η) (hη₀ : η ≤ η₀)
    (hσ₀ : 1 / 2 < σ₀) (hσ : σ₀ ≤ σ) (hσ₁ : σ ≤ 1) (hδ : 1 / 2 ≤ δ)
    (hκ : 0 ≤ κ) (hκ₁ : κ ≤ 1)
    (hκ₂ : κ ≤ kadiriKappa₂ θ η₀ (2 * σ₀ - 1) δ)
    (hκ₃ : κ ≤ kadiriKappa₃ θ η₀ (2 * σ₀ - 1) δ)
    (hc : 0 < σ₀ - η₀ + δ) (hz : z ≤ (σ - 1) / η) (hH : 0 < H)
    (hgap : 0 ≤ 2 * σ₀ - 1 - κ * (1 + 2 * δ))
    (hcut : κ * (1 + 2 * δ) + 1 - σ₀ ≤
      (2 * σ₀ - 1 - κ * (1 + 2 * δ)) * H ^ 2)
    (S : Finset ℕ) (h₀ : 0 ∈ S) (h₁ : 1 ∈ S) (a : ℕ → ℝ)
    (ha : ∀ i ∈ S, 0 ≤ a i) (p : RiemannXiDivisorZeroIndex)
    (hβ : 1 / 2 < (riemannXiDivisorZeroValue p).re)
    (hηρ : η = 1 - (riemannXiDivisorZeroValue p).re)
    (hpoly : ∀ u : ℝ, 0 ≤ ∑ i ∈ S, a i * Real.cos ((i : ℝ) * u))
    (hσA : 1 - 1 / (R * Real.log A) ≤ σ)
    (hlow : ∀ q : RiemannXiDivisorZeroIndex,
      |(riemannXiDivisorZeroValue q).im| < T → (riemannXiDivisorZeroValue q).re ≤ σ)
    (hhigh : ∀ q : RiemannXiDivisorZeroIndex,
      T ≤ |(riemannXiDivisorZeroValue q).im| →
        1 / (R * Real.log |(riemannXiDivisorZeroValue q).im|) ≤
          1 - (riemannXiDivisorZeroValue q).re)
    (hharm : ∀ i ∈ S, |(i : ℝ) * (riemannXiDivisorZeroValue p).im| + H ≤ A)
    (ht : 10 ^ 9 ≤ (riemannXiDivisorZeroValue p).im)

include hR hT hθ hη hη₀ hσ₀ hσ hσ₁ hδ hκ hκ₁ hκ₂ hκ₃ hc hz hH hgap hcut
  h₀ h₁ ha hβ hηρ hpoly hσA hlow hhigh hharm ht

/-- The actual distinguished zero satisfies the normalized bootstrap inequality. -/
theorem kadiri_actual_bootstrap_constraint :
    kadiriTransformGap θ (a 0) (a 1) ((1 - σ) / η) ≤
      kadiriBootstrapLogCoefficient θ κ S a * η * Real.log (riemannXiDivisorZeroValue p).im +
      kadiriBootstrapCorrection θ η η₀ σ₀ σ κ δ z H
        (riemannXiDivisorZeroValue p).im S a := by
  have htpos : 0 < (riemannXiDivisorZeroValue p).im := by linarith
  have hA : ∀ i ∈ S, (i : ℝ) * (riemannXiDivisorZeroValue p).im ≠ 0 →
      10 ^ 9 ≤ |(i : ℝ) * (riemannXiDivisorZeroValue p).im| + H := by
    intro i _ hi
    have hi₀ : i ≠ 0 := by intro he; subst i; simp at hi
    have hi₁ : (1 : ℝ) ≤ i := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hi₀
    rw [abs_of_nonneg (mul_nonneg (Nat.cast_nonneg i) htpos.le)]
    nlinarith [mul_le_mul_of_nonneg_right hi₁ htpos.le]
  have hm := kadiriWeight_region_master_nonneg hR hT hθ hη hη₀ hσ₀ hσ hσ₁ hδ
    hκ hκ₁ hκ₂ hκ₃ hc hz hH hgap hcut S a (fun i : ℕ => (i : ℝ)) ha
    1 h₁ (by norm_num) p hβ hηρ hpoly hσA hlow hhigh hharm hA
  have hg := kadiriTransformGap_le_budget_of_master hθ hη hηρ htpos.ne' S h₀ a hm
  rwa [kadiriBootstrapBudget_eq_log_add_correction hθ hη htpos S h₀ a] at hg

/-- Once the explicit margin is verified, the actual zero obeys the improved region. -/
theorem xi_zero_gap_of_bootstrap_margin {Rnext : ℝ} (hRnext : 0 < Rnext)
    (hκstrict : κ < 1) (ha₁ : 0 < a 1)
    (hmargin : kadiriBootstrapLogCoefficient θ κ S a / Rnext ≤
      kadiriTransformGap θ (a 0) (a 1) ((1 - σ) / η) -
        kadiriBootstrapCorrection θ η η₀ σ₀ σ κ δ z H
          (riemannXiDivisorZeroValue p).im S a) :
    1 / (Rnext * Real.log (riemannXiDivisorZeroValue p).im) ≤
      1 - (riemannXiDivisorZeroValue p).re := by
  have hm := kadiri_actual_bootstrap_constraint hR hT hθ hη hη₀ hσ₀ hσ hσ₁ hδ
    hκ hκ₁ hκ₂ hκ₃ hc hz hH hgap hcut
    S h₀ h₁ a ha p hβ hηρ hpoly hσA hlow hhigh hharm ht
  have hcpos := kadiriBootstrapLogCoefficient_pos hθ hκstrict S h₁ a ha ha₁
  simpa only [hηρ] using
    kadiri_gap_of_bootstrap_margin S a hcpos hRnext (by linarith) hm hmargin

end

end PrimeFactorUnimodality
