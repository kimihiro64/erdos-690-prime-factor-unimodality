import PrimeFactorUnimodality.Helpers.Analytic.KadiriBootstrapMaster

/-! # Uniform tail and moment-envelope regressions

Check exact threshold endpoints, arbitrary harmonics, the retained zero
mode, pole monotonicity, actual moment substitution, and scale-endpoint
control of a polynomial with an unrestricted signed linear coefficient.
-/

namespace PrimeFactorUnimodality.Tests

noncomputable section

open Real

example {T H : ℝ} (hT : 0 < T) (hH : 0 < H) : 0 ≤ xiLehmanLogCoefficient T H :=
  xiLehmanLogCoefficient_nonneg hT hH

example {T H : ℝ} (hT : 0 < T) (hH : 0 < H) : 0 ≤ xiLehmanAffineConstant T H :=
  xiLehmanAffineConstant_nonneg hT hH

example {T t H : ℝ} (hT : 2 ≤ T) (ht : T ≤ t) (hH : 4 ≤ H) :
    xiLehmanHighBound t H ≤ xiLehmanLogCoefficient T H * Real.log t +
      xiLehmanAffineConstant T H := xiLehmanHighBound_le_affine hT ht hH

example : xiLehmanHighBound 2 4 ≤
    xiLehmanLogCoefficient 2 4 * Real.log 2 + xiLehmanAffineConstant 2 4 :=
  xiLehmanHighBound_le_affine le_rfl le_rfl le_rfl

example {T H : ℝ} (hT : 2 ≤ T) (hH : 4 ≤ H) :
    xiLehmanHighBound T H ≤ xiLehmanLogCoefficient T H * Real.log T +
      xiLehmanAffineConstant T H := xiLehmanHighBound_le_affine hT le_rfl hH

example (S : Finset ℕ) (a : ℕ → ℝ) (ha : ∀ i ∈ S, 0 ≤ a i) (t : ℝ) :
    0 ≤ kadiriPoleCoefficient S a t := kadiriPoleCoefficient_nonneg S a ha t

example (S : Finset ℕ) (a : ℕ → ℝ) (ha : ∀ i ∈ S, 0 ≤ a i)
    {T t : ℝ} (hT : 0 < T) (ht : T ≤ t) :
    kadiriPoleCoefficient S a t ≤ kadiriPoleCoefficient S a T :=
  antitoneOn_kadiriPoleCoefficient S a ha hT (hT.trans_le ht) ht

example (a : ℕ → ℝ) (t : ℝ) : kadiriPoleCoefficient {0} a t = 0 := by
  simp [kadiriPoleCoefficient]

example (T H : ℝ) (a : ℕ → ℝ) : kadiriTailLogCoefficient T H {0} a = 0 := by
  simp [kadiriTailLogCoefficient]

example (T H : ℝ) (a : ℕ → ℝ) :
    kadiriTailAffineConstant T H {0} a = a 0 * xiLehmanTailMajorant 0 H := by
  simp [kadiriTailAffineConstant]

example {T H : ℝ} (hT : 0 < T) (hH : 0 < H) (n : ℕ)
    (a : ℕ → ℝ) (ha : ∀ i ∈ Finset.range (n + 1), 0 ≤ a i) :
    0 ≤ kadiriTailAffineConstant T H (Finset.range (n + 1)) a :=
  kadiriTailAffineConstant_nonneg hT hH _ (by simp) a ha

example {T t H : ℝ} (hT : 2 ≤ T) (ht : T ≤ t) (hH : 4 ≤ H) (n : ℕ)
    (a : ℕ → ℝ) (ha : ∀ i ∈ Finset.range (n + 1), 0 ≤ a i) :
    (∑ i ∈ Finset.range (n + 1), a i * xiLehmanTailMajorant ((i : ℝ) * t) H) ≤
      kadiriTailLogCoefficient T H (Finset.range (n + 1)) a * Real.log t +
        kadiriTailAffineConstant T H (Finset.range (n + 1)) a :=
  sum_xiLehmanTailMajorant_le_affine hT ht hH _ (by simp) a ha

example {t H : ℝ} (ht : 10 ^ 9 ≤ t) (hH : 0 < H)
    (S : Finset ℕ) (a : ℕ → ℝ) (ha : ∀ i ∈ S, 0 ≤ a i) :
    0 ≤ ∑ i ∈ S, a i * xiLehmanTailMajorant ((i : ℝ) * t) H :=
  sum_xiLehmanTailMajorant_nonneg ht hH S a ha

example {θ z y B₀ B₁ B₂ B₃ : ℝ} (hθ : π / 2 < θ ∧ θ < π)
    (hz : z ≤ 0) (hy : 0 < y) (hzy : -z * kadiriSupport θ ≤ y)
    (hend : Real.exp y ≤ 1 + y + y ^ 2 / 2 + y ^ 3 / (345 / 100))
    (h₀ : kadiriDerivativeMoment θ 0 ≤ B₀) (h₁ : kadiriDerivativeMoment θ 1 ≤ B₁)
    (h₂ : kadiriDerivativeMoment θ 2 ≤ B₂) (h₃ : kadiriDerivativeMoment θ 3 ≤ B₃) :
    kadiriDerivativeMass θ z ≤ kadiriMomentMassBound z B₀ B₁ B₂ B₃ :=
  kadiriDerivativeMass_le_momentMassBound hθ hz hy hzy hend h₀ h₁ h₂ h₃

example (B₀ B₁ B₂ B₃ : ℝ) : kadiriMomentMassBound 0 B₀ B₁ B₂ B₃ = B₀ := by
  simp [kadiriMomentMassBound]

example {κ σ₀ σ : ℝ} (hκ : 0 ≤ κ) (hσ₀ : -2 < σ₀) (hσ : σ₀ ≤ σ) (t : ℝ) :
    smoothedGammaFactorError κ σ t ≤ smoothedGammaFactorError κ σ₀ t :=
  antitoneOn_smoothedGammaFactorError_sigma hκ t hσ₀ (hσ₀.trans_le hσ) hσ

example {κ σ₀ σ T t : ℝ} (hκ : 0 ≤ κ) (hκ₁ : κ ≤ 1)
    (hσ₀ : -2 < σ₀) (hσ : σ₀ ≤ σ) (hT : 0 < T) (hTt : T ≤ t)
    (S : Finset ℕ) (a : ℕ → ℝ) (ha : ∀ i ∈ S, 0 ≤ a i) :
    kadiriGammaResidual κ σ t S a ≤ kadiriGammaResidual κ σ₀ T S a :=
  (antitoneOn_kadiriGammaResidual hκ hκ₁ σ S a ha hT (hT.trans_le hTt) hTt).trans
    (antitoneOn_kadiriGammaResidual_sigma hκ T S a ha hσ₀ (hσ₀.trans_le hσ) hσ)

example {θ η η₀ σ₀ σ κ δ z H T t y B₀ B₁ B₂ B₃ q : ℝ}
    (hθ : π / 2 < θ ∧ θ < π) (hη : 0 ≤ η) (hσ₀ : 1 / 2 < σ₀) (hσ : σ₀ ≤ σ)
    (hκ : 0 ≤ κ) (hκ₁ : κ ≤ 1) (hT : 2 ≤ T) (hTt : T ≤ t) (ht : 10 ^ 9 ≤ t)
    (hH : 4 ≤ H) (hz : z ≤ 0) (hy : 0 < y) (hzy : -z * kadiriSupport θ ≤ y)
    (hend : Real.exp y ≤ 1 + y + y ^ 2 / 2 + y ^ 3 / (345 / 100))
    (hB₀ : kadiriDerivativeMoment θ 0 ≤ B₀) (hB₁ : kadiriDerivativeMoment θ 1 ≤ B₁)
    (hB₂ : kadiriDerivativeMoment θ 2 ≤ B₂) (hB₃ : kadiriDerivativeMoment θ 3 ≤ B₃)
    (S : Finset ℕ) (h₀ : 0 ∈ S) (a : ℕ → ℝ) (ha : ∀ i ∈ S, 0 ≤ a i)
    (hq : η * Real.log t ≤ q) :
    kadiriBootstrapCorrection θ η η₀ σ₀ σ κ δ z H t S a ≤
      kadiriMomentCorrectionPolynomial θ η η₀ σ₀ κ δ z H T B₀ B₁ B₂ B₃ q S a :=
  kadiriBootstrapCorrection_le_momentPolynomial hθ hη hσ₀ hσ hκ hκ₁ hT hTt ht hH hz
    hy hzy hend hB₀ hB₁ hB₂ hB₃ S h₀ a ha hq

example (θ η₀ σ₀ κ δ M P L₀ L₁ G q : ℝ) (S : Finset ℕ) (a : ℕ → ℝ) :
    kadiriCorrectionPolynomial θ 0 η₀ σ₀ κ δ M P L₀ L₁ G q S a = 0 := by
  simp [kadiriCorrectionPolynomial]

example {θ η η₀ σ₀ κ δ M P L₀ L₁ G q : ℝ} {S : Finset ℕ} {a : ℕ → ℝ}
    (hη : 0 ≤ η) (hη₀ : 0 < η₀) (hηη₀ : η ≤ η₀)
    (h₂ : 0 ≤ kadiriCorrectionQuadratic θ σ₀ κ M P L₀ L₁ q)
    (h₃ : 0 ≤ kadiriCorrectionCubic θ η₀ σ₀ κ δ L₀ S a)
    (hend : kadiriCorrectionPolynomial θ η₀ η₀ σ₀ κ δ M P L₀ L₁ G q S a ≤ 0) :
    kadiriCorrectionPolynomial θ η η₀ σ₀ κ δ M P L₀ L₁ G q S a ≤ 0 :=
  kadiriCorrectionPolynomial_nonpos_of_endpoint hη hη₀ hηη₀ h₂ h₃ hend

end

end PrimeFactorUnimodality.Tests
