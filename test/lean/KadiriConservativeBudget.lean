import PrimeFactorUnimodality.Helpers.Analytic.KadiriConservativeBudget

/-! # Elementary correction-budget regressions

Check empty low-height ranges, vanishing zero-harmonic weight, zero scale,
zero moments, and monotonicity with otherwise unrestricted signed terms.
The numerical zero-free margins are not assumptions of these comparisons.
-/

namespace PrimeFactorUnimodality.Tests

noncomputable section

open Real

example (H : ℝ) : 0 ≤ xiLowReciprocalMass H := xiLowReciprocalMass_nonneg H

example {H : ℝ} (hH : H ≤ 0) : xiLowReciprocalMass H = 0 := by
  apply Finset.sum_eq_zero
  intro p hp
  have h := (mem_xiLowHeightIndices H p).mp hp
  linarith [abs_nonneg (riemannXiDivisorZeroValue p).im]

example (H : ℝ) : xiLehmanTailMajorant 0 H ≤
    (1 + 1 / H ^ 2) * (8 / 3 - Real.log (4 * π)) :=
  xiLehmanTailMajorant_zero_le_elementary H

example : xiLehmanZeroElementaryBound 0 = 8 / 3 - Real.log (4 * π) := by
  simp [xiLehmanZeroElementaryBound]

example (H : ℝ) : xiLehmanZeroElementaryBound (-H) = xiLehmanZeroElementaryBound H := by
  simp [xiLehmanZeroElementaryBound]

example (T H : ℝ) (S : Finset ℕ) (a : ℕ → ℝ) (ha : 0 ≤ a 0) :
    kadiriTailAffineConstant T H S a ≤ kadiriTailConservativeConstant T H S a :=
  kadiriTailAffineConstant_le_conservative T H S a ha

example (T H : ℝ) (S : Finset ℕ) (a : ℕ → ℝ) (ha : a 0 = 0) :
    kadiriTailAffineConstant T H S a = kadiriTailConservativeConstant T H S a := by
  simp [kadiriTailAffineConstant, kadiriTailConservativeConstant, ha]

example {θ η η₀ σ₀ κ δ M P L₀ L₀' L₁ G q : ℝ}
    (hθ : π / 2 < θ ∧ θ < π) (hη : 0 ≤ η) (hσ : 1 / 2 < σ₀)
    (hκ : 0 ≤ κ) (hM : 0 ≤ M) (hL : L₀ ≤ L₀') (S : Finset ℕ) (a : ℕ → ℝ) :
    kadiriCorrectionPolynomial θ η η₀ σ₀ κ δ M P L₀ L₁ G q S a ≤
      kadiriCorrectionPolynomial θ η η₀ σ₀ κ δ M P L₀' L₁ G q S a :=
  kadiriCorrectionPolynomial_mono_tail hθ hη hσ hκ hM hL S a

example {z B₀ B₁ B₂ B₃ : ℝ} (hz : z ≤ 0)
    (h₀ : 0 ≤ B₀) (h₁ : 0 ≤ B₁) (h₂ : 0 ≤ B₂) (h₃ : 0 ≤ B₃) :
    0 ≤ kadiriMomentMassBound z B₀ B₁ B₂ B₃ :=
  kadiriMomentMassBound_nonneg hz h₀ h₁ h₂ h₃

example (z : ℝ) : kadiriMomentMassBound z 0 0 0 0 = 0 := by
  simp [kadiriMomentMassBound]

example (θ η₀ σ₀ κ δ z H T B₀ B₁ B₂ B₃ q : ℝ) (S : Finset ℕ) (a : ℕ → ℝ) :
    kadiriConservativeMomentPolynomial θ 0 η₀ σ₀ κ δ z H T B₀ B₁ B₂ B₃ q S a = 0 := by
  simp [kadiriConservativeMomentPolynomial, kadiriCorrectionPolynomial]

example {θ η η₀ σ₀ κ δ z H T B₀ B₁ B₂ B₃ q : ℝ}
    (hθ : π / 2 < θ ∧ θ < π) (hη : 0 ≤ η) (hσ : 1 / 2 < σ₀) (hκ : 0 ≤ κ)
    (hM : 0 ≤ kadiriMomentMassBound z B₀ B₁ B₂ B₃)
    (S : Finset ℕ) (a : ℕ → ℝ) (ha : 0 ≤ a 0) :
    kadiriMomentCorrectionPolynomial θ η η₀ σ₀ κ δ z H T B₀ B₁ B₂ B₃ q S a ≤
      kadiriConservativeMomentPolynomial θ η η₀ σ₀ κ δ z H T B₀ B₁ B₂ B₃ q S a :=
  kadiriMomentCorrectionPolynomial_le_conservative hθ hη hσ hκ hM S a ha

end

end PrimeFactorUnimodality.Tests
