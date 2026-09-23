import PrimeFactorUnimodality.Helpers.Analytic.KadiriBootstrapCorrection
import PrimeFactorUnimodality.Helpers.Analytic.KadiriTailEnvelope

/-! # A uniform cubic envelope for the complete bootstrap correction

Combine a logarithmic tail bound with `eta*log(t)<=q`. This upper bound
has to be justified by the target-gap argument, not by the previous
zero-free region, which gives a lower bound instead. The signed linear
term is retained. All monotone substitutions use proved nonnegative
coefficients, including the actual weighted tail and derivative mass.
-/

namespace PrimeFactorUnimodality

noncomputable section

open Real

/-- The linear coefficient, retaining the signed Gamma and retained-pair terms. -/
def kadiriCorrectionLinear (θ η₀ σ₀ κ δ G M L₁ q a₁ : ℝ) : ℝ :=
  kadiriKernel θ 0 * (a₁ * (κ * (1 / δ + 1 / (σ₀ - η₀ + δ)) - 1) + G) + M * L₁ * q / 2

/-- The quadratic coefficient after absorbing one scale times logarithm. -/
def kadiriCorrectionQuadratic (θ σ₀ κ M P L₀ L₁ q : ℝ) : ℝ :=
  M * (P + L₀ / 2) + (-kadiriKernel₂ θ 0) *
    ((1 + 2 * κ) / (2 * (σ₀ - 1 / 2))) * L₁ * q

/-- The cubic coefficient contains the constant tail and smoothed Gamma remainder. -/
def kadiriCorrectionCubic (θ η₀ σ₀ κ δ L₀ : ℝ) (S : Finset ℕ) (a : ℕ → ℝ) : ℝ :=
  (-kadiriKernel₂ θ 0) *
    (a 1 * (1 + κ * (1 / δ ^ 3 + 1 / (σ₀ - η₀ + δ) ^ 3)) +
      ((1 + 2 * κ) / (2 * (σ₀ - 1 / 2))) * L₀ + (∑ i ∈ S, a i) * (1 + κ) / 4)

/-- The complete explicit polynomial upper envelope in the positive scale. -/
def kadiriCorrectionPolynomial (θ η η₀ σ₀ κ δ M P L₀ L₁ G q : ℝ)
    (S : Finset ℕ) (a : ℕ → ℝ) : ℝ :=
  kadiriCorrectionLinear θ η₀ σ₀ κ δ G M L₁ q (a 1) * η +
    kadiriCorrectionQuadratic θ σ₀ κ M P L₀ L₁ q * η ^ 2 +
    kadiriCorrectionCubic θ η₀ σ₀ κ δ L₀ S a * η ^ 3

/-- Proved scalar bounds on the actual terms yield the complete cubic correction envelope. -/
theorem kadiriBootstrapCorrection_le_polynomial {θ η η₀ σ₀ σ κ δ z H t M P L₀ L₁ G q : ℝ}
    (hθ : π / 2 < θ ∧ θ < π) (hη : 0 ≤ η) (hσ₀ : 1 / 2 < σ₀) (hκ : 0 ≤ κ)
    (ht : 10 ≤ t) (hH : 0 < H) (S : Finset ℕ) (a : ℕ → ℝ)
    (ha : ∀ i ∈ S, 0 ≤ a i) (hM : kadiriDerivativeMass θ z ≤ M)
    (hP : kadiriPoleCoefficient S a t ≤ P)
    (hL : (∑ i ∈ S, a i * xiLehmanTailMajorant ((i : ℝ) * t) H) ≤ L₀ + L₁ * Real.log t)
    (hG : kadiriGammaResidual κ σ t S a ≤ G) (hL₁ : 0 ≤ L₁) (hq : η * Real.log t ≤ q) :
    kadiriBootstrapCorrection θ η η₀ σ₀ σ κ δ z H t S a ≤
      kadiriCorrectionPolynomial θ η η₀ σ₀ κ δ M P L₀ L₁ G q S a := by
  let F := a 1 * (κ * (1 / δ + 1 / (σ₀ - η₀ + δ)) - 1)
  let E := (1 + 2 * κ) / (2 * (σ₀ - 1 / 2))
  let D := a 1 * (1 + κ * (1 / δ ^ 3 + 1 / (σ₀ - η₀ + δ) ^ 3)) +
    (∑ i ∈ S, a i) * (1 + κ) / 4
  have hE : 0 ≤ E := div_nonneg (by linarith) (by linarith)
  have hm : 0 ≤ -kadiriKernel₂ θ 0 := neg_kadiriKernel₂_zero_nonneg hθ
  have hM₀ := (kadiriDerivativeMass_nonneg hθ z).trans hM
  have htail := sum_xiLehmanTailMajorant_nonneg ht hH S a ha
  have hpole := kadiriPoleCoefficient_nonneg S a ha t
  have hfirst := mul_le_mul_of_nonneg_left (add_le_add (le_refl F) hG)
    (mul_nonneg hη (kadiriKernel_zero_pos hθ).le)
  have hsecond := mul_le_mul_of_nonneg_left
    (mul_le_mul hM (add_le_add hP
      (div_le_div_of_nonneg_right hL (by norm_num : (0 : ℝ) ≤ 2)))
      (add_nonneg hpole (div_nonneg htail (by norm_num))) hM₀) (sq_nonneg η)
  have hthird := mul_le_mul_of_nonneg_left
    (add_le_add (le_refl D) (mul_le_mul_of_nonneg_left hL hE))
    (mul_nonneg (pow_nonneg hη 3) hm)
  have hb : kadiriBootstrapCorrection θ η η₀ σ₀ σ κ δ z H t S a ≤
      η * kadiriKernel θ 0 * (F + G) + η ^ 2 * M * (P + (L₀ + L₁ * Real.log t) / 2) +
      η ^ 3 * (-kadiriKernel₂ θ 0) * (D + E * (L₀ + L₁ * Real.log t)) := by
    convert! add_le_add (add_le_add hfirst hsecond) hthird using 1 <;>
      dsimp only [kadiriBootstrapCorrection, F, E, D] <;> ring
  have hlog₂ := mul_le_mul_of_nonneg_left hq
    (div_nonneg (mul_nonneg (mul_nonneg hη hM₀) hL₁) (by norm_num : (0 : ℝ) ≤ 2))
  have hlog₃ := mul_le_mul_of_nonneg_left hq
    (mul_nonneg (mul_nonneg (mul_nonneg (sq_nonneg η) hm) hE) hL₁)
  have hsecond' : η ^ 2 * M * (P + (L₀ + L₁ * Real.log t) / 2) ≤
      η ^ 2 * M * (P + L₀ / 2) + η * (M * L₁ * q / 2) := by
    nlinarith only [hlog₂]
  have hthird' : η ^ 3 * (-kadiriKernel₂ θ 0) * (D + E * (L₀ + L₁ * Real.log t)) ≤
      η ^ 3 * (-kadiriKernel₂ θ 0) * (D + E * L₀) +
        η ^ 2 * (-kadiriKernel₂ θ 0) * E * L₁ * q := by
    nlinarith only [hlog₃]
  apply hb.trans
  apply (add_le_add (add_le_add le_rfl hsecond') hthird').trans_eq
  dsimp only [kadiriCorrectionPolynomial, kadiriCorrectionLinear,
    kadiriCorrectionQuadratic, kadiriCorrectionCubic, F, E, D]
  ring

end

end PrimeFactorUnimodality
