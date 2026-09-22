import PrimeFactorUnimodality.Helpers.Analytic.KadiriMomentEnvelope

/-! # An elementary correction budget without a low-zero mass sum

Dropping the nonnegative finite reciprocal mass increases the zero-height
tail. Mathlib's proved Euler-constant bound `gamma < 2/3` then makes this
tail entirely elementary. The quadratic and cubic correction coefficients
are monotone in that tail constant on the actual parameter domain.
This removes a numerical mass-sum obligation, not the low-height location
hypothesis used elsewhere in the zero-free argument.
-/

namespace PrimeFactorUnimodality

noncomputable section

open Real

/-- Each actual low-height reciprocal atom has nonnegative real part. -/
theorem xiLowReciprocalMass_nonneg (H : ℝ) : 0 ≤ xiLowReciprocalMass H :=
  Finset.sum_nonneg (fun p _ => re_xi_divisor_reciprocal_nonneg p)

/-- A zero-height bound involving only a rational constant, logarithm, and pi. -/
def xiLehmanZeroElementaryBound (H : ℝ) : ℝ :=
  (1 + 1 / H ^ 2) * (8 / 3 - Real.log (4 * π))

/-- The elementary bound dominates the exact finite-subtraction majorant. -/
theorem xiLehmanTailMajorant_zero_le_elementary (H : ℝ) :
    xiLehmanTailMajorant 0 H ≤ xiLehmanZeroElementaryBound H := by
  have hmass := xiLowReciprocalMass_nonneg H
  have hγ := Real.eulerMascheroniConstant_lt_two_thirds.le
  have hscalar : (2 + Real.eulerMascheroniConstant - Real.log (4 * π)) / 2 -
      xiLowReciprocalMass H ≤ (8 / 3 - Real.log (4 * π)) / 2 := by linarith
  have h := mul_le_mul_of_nonneg_left hscalar
    (by positivity : 0 ≤ 2 * (1 + 1 / H ^ 2))
  simp only [xiLehmanTailMajorant, ↓reduceIte]
  exact h.trans_eq (by unfold xiLehmanZeroElementaryBound; ring)

/-- The harmonic tail constant with no zero index or Euler constant to evaluate. -/
def kadiriTailConservativeConstant (T H : ℝ) (S : Finset ℕ) (a : ℕ → ℝ) : ℝ :=
  a 0 * xiLehmanZeroElementaryBound H +
    ∑ i ∈ S.erase 0, a i *
      (xiLehmanLogCoefficient T H * Real.log (i : ℝ) + xiLehmanAffineConstant T H)

/-- Nonnegative zero-harmonic weight preserves the tail-constant comparison. -/
theorem kadiriTailAffineConstant_le_conservative (T H : ℝ) (S : Finset ℕ)
    (a : ℕ → ℝ) (ha₀ : 0 ≤ a 0) :
    kadiriTailAffineConstant T H S a ≤ kadiriTailConservativeConstant T H S a :=
  add_le_add (mul_le_mul_of_nonneg_left
    (xiLehmanTailMajorant_zero_le_elementary H) ha₀) le_rfl

/-- The complete correction increases with the constant term of the tail envelope. -/
theorem kadiriCorrectionPolynomial_mono_tail
    {θ η η₀ σ₀ κ δ M P L₀ L₀' L₁ G q : ℝ}
    (hθ : π / 2 < θ ∧ θ < π) (hη : 0 ≤ η) (hσ₀ : 1 / 2 < σ₀)
    (hκ : 0 ≤ κ) (hM : 0 ≤ M) (hL : L₀ ≤ L₀') (S : Finset ℕ) (a : ℕ → ℝ) :
    kadiriCorrectionPolynomial θ η η₀ σ₀ κ δ M P L₀ L₁ G q S a ≤
      kadiriCorrectionPolynomial θ η η₀ σ₀ κ δ M P L₀' L₁ G q S a := by
  have hm := neg_kadiriKernel₂_zero_nonneg hθ
  have he : 0 ≤ (1 + 2 * κ) / (2 * (σ₀ - 1 / 2)) :=
    div_nonneg (by linarith) (by linarith)
  have h₂ := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left
      (div_le_div_of_nonneg_right hL (by norm_num : (0 : ℝ) ≤ 2)) hM) (sq_nonneg η)
  have h₃ := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hL he) hm) (pow_nonneg hη 3)
  unfold kadiriCorrectionPolynomial kadiriCorrectionLinear
    kadiriCorrectionQuadratic kadiriCorrectionCubic
  nlinarith only [h₂, h₃]

/-- Nonnegative moment bounds give a nonnegative mass envelope for nonpositive transform shift. -/
theorem kadiriMomentMassBound_nonneg {z B₀ B₁ B₂ B₃ : ℝ}
    (hz : z ≤ 0) (h₀ : 0 ≤ B₀) (h₁ : 0 ≤ B₁) (h₂ : 0 ≤ B₂) (h₃ : 0 ≤ B₃) :
    0 ≤ kadiriMomentMassBound z B₀ B₁ B₂ B₃ := by
  have he : kadiriMomentMassBound z B₀ B₁ B₂ B₃ =
      B₀ + B₁ * (-z) + B₂ * (-z) ^ 2 / 2 + B₃ * (-z) ^ 3 / (345 / 100) := by
    unfold kadiriMomentMassBound
    ring
  rw [he]
  have hz' : 0 ≤ -z := neg_nonneg.mpr hz
  positivity

/-- The elementary endpoint polynomial, with no finite zero sum remaining. -/
def kadiriConservativeMomentPolynomial (θ η η₀ σ₀ κ δ z H T B₀ B₁ B₂ B₃ q : ℝ)
    (S : Finset ℕ) (a : ℕ → ℝ) : ℝ :=
  kadiriCorrectionPolynomial θ η η₀ σ₀ κ δ (kadiriMomentMassBound z B₀ B₁ B₂ B₃)
    (kadiriPoleCoefficient S a T) (kadiriTailConservativeConstant T H S a)
    (kadiriTailLogCoefficient T H S a) (kadiriGammaResidual κ σ₀ T S a) q S a

/-- The actual moment envelope is at most the elementary conservative polynomial. -/
theorem kadiriMomentCorrectionPolynomial_le_conservative
    {θ η η₀ σ₀ κ δ z H T B₀ B₁ B₂ B₃ q : ℝ}
    (hθ : π / 2 < θ ∧ θ < π) (hη : 0 ≤ η) (hσ₀ : 1 / 2 < σ₀) (hκ : 0 ≤ κ)
    (hM : 0 ≤ kadiriMomentMassBound z B₀ B₁ B₂ B₃)
    (S : Finset ℕ) (a : ℕ → ℝ) (ha₀ : 0 ≤ a 0) :
    kadiriMomentCorrectionPolynomial θ η η₀ σ₀ κ δ z H T B₀ B₁ B₂ B₃ q S a ≤
      kadiriConservativeMomentPolynomial θ η η₀ σ₀ κ δ z H T B₀ B₁ B₂ B₃ q S a :=
  kadiriCorrectionPolynomial_mono_tail hθ hη hσ₀ hκ hM
    (kadiriTailAffineConstant_le_conservative T H S a ha₀) S a

end

end PrimeFactorUnimodality
