import PrimeFactorUnimodality.Helpers.Analytic.KadiriMomentEnvelope

/-! # Reducing correction nonpositivity to a scale endpoint

The quadratic and cubic coefficients of the envelope are nonnegative
on the actual parameter domain. After factoring out the positive scale,
the remaining quadratic expression increases with scale. A nonpositive
budget at the maximum scale therefore controls all smaller scales,
without assuming the signed linear coefficient is nonnegative.
-/

namespace PrimeFactorUnimodality

noncomputable section

open Real

/-- Every term of the quadratic coefficient is nonnegative under the actual sign conditions. -/
theorem kadiriCorrectionQuadratic_nonneg {θ σ₀ κ M P L₀ L₁ q : ℝ}
    (hθ : π / 2 < θ ∧ θ < π) (hσ₀ : 1 / 2 < σ₀) (hκ : 0 ≤ κ)
    (hM : 0 ≤ M) (hP : 0 ≤ P) (hL₀ : 0 ≤ L₀) (hL₁ : 0 ≤ L₁) (hq : 0 ≤ q) :
    0 ≤ kadiriCorrectionQuadratic θ σ₀ κ M P L₀ L₁ q := by
  have hm := neg_kadiriKernel₂_zero_nonneg hθ
  have he : 0 ≤ (1 + 2 * κ) / (2 * (σ₀ - 1 / 2)) :=
    div_nonneg (by linarith) (by linarith)
  exact add_nonneg (mul_nonneg hM (add_nonneg hP (div_nonneg hL₀ (by norm_num))))
    (mul_nonneg (mul_nonneg (mul_nonneg hm he) hL₁) hq)

/-- The cubic coefficient is nonnegative; the signed linear coefficient is not used here. -/
theorem kadiriCorrectionCubic_nonneg {θ η₀ σ₀ κ δ L₀ : ℝ}
    (hθ : π / 2 < θ ∧ θ < π) (hσ₀ : 1 / 2 < σ₀) (hκ : 0 ≤ κ)
    (hδ : 0 < δ) (hc : 0 < σ₀ - η₀ + δ) (hL₀ : 0 ≤ L₀)
    (S : Finset ℕ) (h₁ : 1 ∈ S) (a : ℕ → ℝ) (ha : ∀ i ∈ S, 0 ≤ a i) :
    0 ≤ kadiriCorrectionCubic θ η₀ σ₀ κ δ L₀ S a := by
  have hm := neg_kadiriKernel₂_zero_nonneg hθ
  have ha₁ := ha 1 h₁
  have hs := Finset.sum_nonneg ha
  have hden : 0 < σ₀ - 1 / 2 := by linarith
  unfold kadiriCorrectionCubic
  positivity

/-- A nonpositive endpoint budget controls the entire positive scale interval. -/
theorem kadiriCorrectionPolynomial_nonpos_of_endpoint
    {θ η η₀ σ₀ κ δ M P L₀ L₁ G q : ℝ} {S : Finset ℕ} {a : ℕ → ℝ}
    (hη : 0 ≤ η) (hη₀ : 0 < η₀) (hηη₀ : η ≤ η₀)
    (h₂ : 0 ≤ kadiriCorrectionQuadratic θ σ₀ κ M P L₀ L₁ q)
    (h₃ : 0 ≤ kadiriCorrectionCubic θ η₀ σ₀ κ δ L₀ S a)
    (hend : kadiriCorrectionPolynomial θ η₀ η₀ σ₀ κ δ M P L₀ L₁ G q S a ≤ 0) :
    kadiriCorrectionPolynomial θ η η₀ σ₀ κ δ M P L₀ L₁ G q S a ≤ 0 := by
  let c₁ := kadiriCorrectionLinear θ η₀ σ₀ κ δ G M L₁ q (a 1)
  let c₂ := kadiriCorrectionQuadratic θ σ₀ κ M P L₀ L₁ q
  let c₃ := kadiriCorrectionCubic θ η₀ σ₀ κ δ L₀ S a
  have hfactor : η₀ * (c₁ + c₂ * η₀ + c₃ * η₀ ^ 2) ≤ η₀ * 0 := by
    convert! hend using 1
    · dsimp only [c₁, c₂, c₃, kadiriCorrectionPolynomial]
      ring
    · ring
  have hinner := le_of_mul_le_mul_left hfactor hη₀
  have hmono : c₁ + c₂ * η + c₃ * η ^ 2 ≤ c₁ + c₂ * η₀ + c₃ * η₀ ^ 2 :=
    add_le_add (add_le_add le_rfl (mul_le_mul_of_nonneg_left hηη₀ h₂))
      (mul_le_mul_of_nonneg_left ((sq_le_sq₀ hη hη₀.le).mpr hηη₀) h₃)
  have h := mul_nonpos_of_nonneg_of_nonpos hη (hmono.trans hinner)
  convert! h using 1
  dsimp only [c₁, c₂, c₃, kadiriCorrectionPolynomial]
  ring

end

end PrimeFactorUnimodality
