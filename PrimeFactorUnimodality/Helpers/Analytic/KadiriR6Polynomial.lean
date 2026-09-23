import PrimeFactorUnimodality.Helpers.Analytic.KadiriR6Parameters

/-! # A uniform negative cubic correction from coarse scalar budgets

The signed linear term dominates the quadratic and cubic terms throughout
the actual endpoint-scale interval. Bound the three coefficients separately;
in particular, do not treat the negative Gamma term as an absolute error.
The theorem also includes the zero-scale boundary.
-/

namespace PrimeFactorUnimodality

noncomputable section

open Finset Real

/-- The shared elementary moment mass is bounded by the derivative maximum and support length. -/
theorem kadiriSix_moment_mass_le
    (hm : -kadiriKernel₂ (185573 / 100000) 0 ≤ (1163 : ℝ))
    (hd : kadiriSupport (185573 / 100000) ≤ (109 / 100 : ℝ)) :
    kadiriMomentMassBound (-1)
      (kadiriDerivativeMomentElementary (185573 / 100000) 0)
      (kadiriDerivativeMomentElementary (185573 / 100000) 1)
      (kadiriDerivativeMomentElementary (185573 / 100000) 2)
      (kadiriDerivativeMomentElementary (185573 / 100000) 3) ≤ 3000 := by
  let d := kadiriSupport (185573 / 100000)
  let m := -kadiriKernel₂ (185573 / 100000) 0
  have hd₀ : 0 ≤ d := (kadiriSupport_pos mossinghoffTrudgian_theta_mem).le
  have hm₀ : 0 ≤ m := neg_kadiriKernel₂_zero_nonneg mossinghoffTrudgian_theta_mem
  have he : kadiriMomentMassBound (-1)
      (kadiriDerivativeMomentElementary (185573 / 100000) 0)
      (kadiriDerivativeMomentElementary (185573 / 100000) 1)
      (kadiriDerivativeMomentElementary (185573 / 100000) 2)
      (kadiriDerivativeMomentElementary (185573 / 100000) 3) =
      m * (d + d ^ 2 / 2 + d ^ 3 / 6 + d ^ 4 / (4 * (345 / 100))) := by
    simp only [kadiriMomentMassBound, kadiriDerivativeMomentElementary]
    dsimp [m, d]
    norm_num
    ring
  rw [he]
  calc
    _ ≤ (1163 : ℝ) * (109 / 100 + (109 / 100) ^ 2 / 2 +
        (109 / 100) ^ 3 / 6 + (109 / 100) ^ 4 / (4 * (345 / 100))) := by gcongr
    _ ≤ 3000 := by norm_num

/-- Coarse rational bounds force the complete cubic correction to be nonpositive. -/
theorem kadiriSix_polynomial_nonpos {η σ M P L₀ L₁ G q : ℝ}
    (hη : 0 ≤ η) (hη' : η ≤ 98 / 10000) (hσ : 9922 / 10000 ≤ σ)
    (hM' : M ≤ 3000) (hP : 0 ≤ P) (hP' : P ≤ 1 / 1000)
    (hL₀ : 0 ≤ L₀) (hL₀' : L₀ ≤ 1) (hL₁ : 0 ≤ L₁) (hL₁' : L₁ ≤ 1 / 1000)
    (hG : G ≤ -(1 / 4)) (hq : 0 ≤ q) (hq' : q ≤ 1 / 6)
    (hg : (1387 / 10 : ℝ) ≤ kadiriKernel (185573 / 100000) 0)
    (hm : -kadiriKernel₂ (185573 / 100000) 0 ≤ (1163 : ℝ)) :
    kadiriCorrectionPolynomial (185573 / 100000) η η σ (437 / 1000) (62 / 100)
      M P L₀ L₁ G q (range 17) mossinghoffTrudgianCoefficient ≤ 0 := by
  let g := kadiriKernel (185573 / 100000) 0
  let m := -kadiriKernel₂ (185573 / 100000) 0
  let E := (1 + 2 * (437 / 1000 : ℝ)) / (2 * (σ - 1 / 2))
  let c := σ - η + (62 / 100 : ℝ)
  have hg₀ : 0 ≤ g := (kadiriKernel_zero_pos mossinghoffTrudgian_theta_mem).le
  have hm₀ : 0 ≤ m := neg_kadiriKernel₂_zero_nonneg mossinghoffTrudgian_theta_mem
  have hE₀ : 0 ≤ E := div_nonneg (by norm_num) (by linarith)
  have hE : E ≤ 2 := by
    apply (div_le_iff₀ (by linarith : 0 < 2 * (σ - 1 / 2))).mpr
    linarith
  have hc : (8 / 5 : ℝ) ≤ c := by dsimp [c]; linarith
  have hcpos : 0 < c := by linarith
  have hcInv : 1 / c ≤ (5 / 8 : ℝ) := by
    apply (div_le_iff₀ hcpos).mpr
    linarith
  have hcCube : 1 / c ^ 3 ≤ (1 : ℝ) := by
    apply (div_le_iff₀ (pow_pos hcpos 3)).mpr
    have h : (1 : ℝ) ^ 3 ≤ c ^ 3 := by gcongr; linarith
    norm_num at h ⊢
    exact h
  have hf : (437 / 1000 : ℝ) * (1 / (62 / 100) + 1 / c) - 1 ≤ 0 := by
    linarith only [hcInv]
  have ha₁ := mossinghoffTrudgianCoefficient_one_pos.le
  have ha₂ : mossinghoffTrudgianCoefficient 1 ≤ 2 := by
    linarith [mossinghoffTrudgianCoefficient_one_bounds.2]
  have hsum : (∑ i ∈ range 17, mossinghoffTrudgianCoefficient i) ≤ 5 := by
    linarith [sum_mossinghoffTrudgianCoefficient_bounds.2]
  have hlin : kadiriCorrectionLinear (185573 / 100000) η σ (437 / 1000)
      (62 / 100) G M L₁ q (mossinghoffTrudgianCoefficient 1) ≤ -34 := by
    have hb : mossinghoffTrudgianCoefficient 1 *
        ((437 / 1000 : ℝ) * (1 / (62 / 100) + 1 / c) - 1) + G ≤ -(1 / 4 : ℝ) := by
      have h := mul_nonpos_of_nonneg_of_nonpos ha₁ hf
      linarith only [h, hG]
    have hmain := mul_le_mul_of_nonneg_left hb hg₀
    have htail : M * L₁ * q / 2 ≤ (1 / 4 : ℝ) := by
      calc
        _ ≤ (3000 : ℝ) * (1 / 1000) * (1 / 6) / 2 := by gcongr
        _ = _ := by norm_num
    change g * (mossinghoffTrudgianCoefficient 1 *
      ((437 / 1000 : ℝ) * (1 / (62 / 100) + 1 / c) - 1) + G) + M * L₁ * q / 2 ≤ -34
    linarith only [hmain, htail, hg]
  have hquad : kadiriCorrectionQuadratic (185573 / 100000) σ (437 / 1000) M P L₀ L₁ q ≤
      1504 := by
    change M * (P + L₀ / 2) + m * E * L₁ * q ≤ 1504
    calc
      _ ≤ (3000 : ℝ) * (1 / 1000 + 1 / 2) + 1163 * 2 * (1 / 1000) * (1 / 6) := by
        gcongr
      _ ≤ _ := by norm_num
  have hcubic : kadiriCorrectionCubic (185573 / 100000) η σ (437 / 1000) (62 / 100)
      L₀ (range 17) mossinghoffTrudgianCoefficient ≤ 13956 := by
    have hb : mossinghoffTrudgianCoefficient 1 *
        (1 + (437 / 1000 : ℝ) * (1 / (62 / 100) ^ 3 + 1 / c ^ 3)) + E * L₀ +
        (∑ i ∈ range 17, mossinghoffTrudgianCoefficient i) * (1 + 437 / 1000) / 4 ≤ 12 := by
      calc
        _ ≤ (2 : ℝ) * (1 + (437 / 1000) * (5 + 1)) + 2 * 1 + 5 * (1 + 437 / 1000) / 4 := by
          gcongr
          norm_num
        _ ≤ _ := by norm_num
    change m * _ ≤ 13956
    have h := mul_le_mul_of_nonneg_left hb hm₀
    have h' := mul_le_mul_of_nonneg_right hm (by norm_num : (0 : ℝ) ≤ 12)
    exact (h.trans h').trans_eq (by norm_num)
  have hsmall : -34 + (1504 : ℝ) * η + 13956 * η ^ 2 ≤ 0 := by
    have hs : η ^ 2 ≤ (98 / 10000 : ℝ) ^ 2 := by nlinarith only [hη, hη']
    nlinarith only [hη', hs]
  have hn := mul_nonpos_of_nonneg_of_nonpos hη hsmall
  have h₁ := mul_le_mul_of_nonneg_right hlin hη
  have h₂ := mul_le_mul_of_nonneg_right hquad (sq_nonneg η)
  have h₃ := mul_le_mul_of_nonneg_right hcubic (pow_nonneg hη 3)
  unfold kadiriCorrectionPolynomial
  nlinarith only [h₁, h₂, h₃, hn]

end

end PrimeFactorUnimodality
