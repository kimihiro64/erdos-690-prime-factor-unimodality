import PrimeFactorUnimodality.Helpers.Analytic.SmoothedGammaBoundary

/-! # A uniform explicit bound for the smoothed Gamma remainder

The proved trivial-pole expansion replaces the boundary integral by a
series of actual Laplace remainders. Two integrations by parts bound each
term, and the pinned PNT inverse-square tail bound sums the majorant.
The result is uniform in the imaginary part and includes the entire
working half-plane `Re(s)>1/2`. No asymptotic constant is introduced.

The comparison reuses `Complex.summable_one_div_natCast_add_one_sq` and
`Complex.tsum_one_div_natCast_add_add_one_sq_le` from Robby Sneiderman's
`DigammaSeries`, at PNT revision `f6147e7572ab3abe5428101bc0b13627bcb005df`.
-/

namespace PrimeFactorUnimodality

noncomputable section

open Complex Real Set

private theorem gamma_remainder_denominator {s : ℂ} (hs : 0 ≤ s.re) (n : ℕ) :
    8 * ((n : ℝ) + 1) ^ 2 ≤ (s - shiftedGammaPole n).re * ‖s - shiftedGammaPole n‖ ^ 2 := by
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hre : (s - shiftedGammaPole n).re = s.re + 2 * ((n : ℝ) + 1) := by
    simp [shiftedGammaPole]
  have htwo : 2 ≤ (s - shiftedGammaPole n).re := by rw [hre]; linarith
  have hnorm : 2 * ((n : ℝ) + 1) ≤ ‖s - shiftedGammaPole n‖ :=
    (by rw [hre]; linarith : 2 * ((n : ℝ) + 1) ≤ (s - shiftedGammaPole n).re).trans
      (re_le_norm _)
  have hsq : 4 * ((n : ℝ) + 1) ^ 2 ≤ ‖s - shiftedGammaPole n‖ ^ 2 := by
    nlinarith [norm_nonneg (s - shiftedGammaPole n)]
  exact (by linarith : 8 * ((n : ℝ) + 1) ^ 2 ≤ 2 * ‖s - shiftedGammaPole n‖ ^ 2).trans
    (mul_le_mul_of_nonneg_right htwo (sq_nonneg _))

/-- A second-derivative bound gives a uniform cubic-scale Gamma remainder. -/
theorem norm_smoothedGammaRemainder_le_quarter
    {f g h : ℝ → ℂ} {d M : ℝ} (hd : 0 ≤ d) (hM : 0 ≤ M)
    (hf : ContinuousOn f (Icc 0 d)) (hg : ContinuousOn g (Icc 0 d))
    (hh : ContinuousOn h (Icc 0 d))
    (hfg : ∀ u ∈ Ioo 0 d, HasDerivAt f (g u) u)
    (hgh : ∀ u ∈ Ioo 0 d, HasDerivAt g (h u) u)
    (hfd : f d = 0) (hg₀ : g 0 = 0) (hgd : g d = 0)
    (hbound : ∀ u ∈ Icc 0 d, ‖h u‖ ≤ M)
    {s : ℂ} (hs : 1 / 2 < s.re) : ‖smoothedGammaRemainder h d s‖ ≤ M / 4 := by
  let F (n : ℕ) := finiteLaplace f d (s - shiftedGammaPole n) - f 0 / (s - shiftedGammaPole n)
  let B (n : ℕ) := M / 8 * (1 / ((n : ℝ) + 1) ^ 2)
  have hB : Summable B := Complex.summable_one_div_natCast_add_one_sq.mul_left (M / 8)
  have hpoint (n : ℕ) : ‖F n‖ ≤ B n := by
    have hp : 0 < (s - shiftedGammaPole n).re := by
      simp only [sub_re]
      linarith [shiftedGammaPole_re_nonpos n]
    apply (norm_finiteLaplace_sub_pole_le_div_re hd hM hf hg hh hfg hgh hfd hg₀ hgd hbound hp).trans
    calc
      _ ≤ M / (8 * ((n : ℝ) + 1) ^ 2) :=
        div_le_div_of_nonneg_left hM (by positivity)
          (gamma_remainder_denominator (by linarith : 0 ≤ s.re) n)
      _ = B n := by dsimp [B]; simp only [div_eq_mul_inv, mul_inv_rev]; ring
  have hnorm := Summable.of_nonneg_of_le (fun n => norm_nonneg (F n)) hpoint hB
  have hsum : (∑' n : ℕ, 1 / ((n : ℝ) + 1) ^ 2) ≤ 2 := by
    have he := Complex.summable_one_div_natCast_add_one_sq.sum_add_tsum_nat_add 1
    have ht := Complex.tsum_one_div_natCast_add_add_one_sq_le (N := 1) (by norm_num)
    norm_num at he ht
    simp only [one_div]
    linarith
  rw [smoothedGammaRemainder_eq_neg_trivialZeroSum hd hM hf hg hh hfg hgh hfd hg₀ hgd hbound hs,
    norm_neg]
  change ‖∑' n, F n‖ ≤ _
  calc
    _ ≤ ∑' n, ‖F n‖ := norm_tsum_le_tsum_norm hnorm
    _ ≤ ∑' n, B n := hnorm.tsum_le_tsum hpoint hB
    _ = M / 8 * ∑' n : ℕ, 1 / ((n : ℝ) + 1) ^ 2 := tsum_mul_left
    _ ≤ M / 8 * 2 := mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = M / 4 := by ring

end

end PrimeFactorUnimodality
