import PrimeFactorUnimodality.Helpers.Analytic.DigammaHadamardIntegral
import PrimeFactorUnimodality.Mathlib.Analysis.Complex.FiniteLaplace.ResolventIntegral

/-! # Evaluation of the shifted gamma contribution for the actual smoothing weight

The endpoint conditions make the pole-subtracted Laplace weight integrable
with quadratic decay and zero integral. Each negative-even pole evaluates
to a shifted Laplace remainder. This identifies the gamma contribution as
the convergent trivial-zero remainder series on every positive contour
strictly left of the transform parameter.
-/

namespace PrimeFactorUnimodality

noncomputable section

open Complex MeasureTheory Set

variable {f g h : ℝ → ℂ} {d M : ℝ}
  (hd : 0 ≤ d) (hM : 0 ≤ M)
  (hf : ContinuousOn f (Icc 0 d)) (hg : ContinuousOn g (Icc 0 d))
  (hh : ContinuousOn h (Icc 0 d))
  (hfg : ∀ u ∈ Ioo 0 d, HasDerivAt f (g u) u)
  (hgh : ∀ u ∈ Ioo 0 d, HasDerivAt g (h u) u)
  (hfd : f d = 0) (hg₀ : g 0 = 0) (hgd : g d = 0)
  (hbound : ∀ u ∈ Icc 0 d, ‖h u‖ ≤ M)
  {s : ℂ} {c : ℝ} (hc : 0 < c) (hcs : c < s.re)

include hd hM hf hg hh hfg hgh hfd hg₀ hgd hbound hc hcs

/-- The evaluated trivial-zero remainders form an absolutely convergent series. -/
theorem summable_finiteLaplace_shiftedGamma_remainders :
    Summable (fun n : ℕ => finiteLaplace f d (s - shiftedGammaPole n) -
      f 0 / (s - shiftedGammaPole n)) := by
  have hC : 0 ≤ M / (s.re - c) * (1 + ‖s‖ / (s.re - c)) ^ 2 :=
    mul_nonneg (div_nonneg hM (sub_pos.mpr hcs).le) (sq_nonneg _)
  let H : ℝ → ℂ := fun t => finiteLaplace f d (s - ((c : ℂ) + (t : ℂ) * I)) -
    f 0 / (s - ((c : ℂ) + (t : ℂ) * I))
  have hsum := summable_integral_norm_mul_hadamardAtoms hc hc hC
    shiftedGammaPole_ne_zero shiftedGammaPole_re_nonpos
    summable_shiftedGammaPole_norm_inv_rpow
    (integrable_finiteLaplace_sub_pole_contour hd hM hf hg hh hfg hgh hfd hg₀ hgd hbound hcs)
    (norm_finiteLaplace_sub_pole_contour_le hd hM hf hg hh hfg hgh hfd hg₀ hgd hbound hc hcs)
  have hi : Summable (fun n : ℕ => ∫ t : ℝ, H t *
      (1 / ((c : ℂ) + (t : ℂ) * I - shiftedGammaPole n) + 1 / shiftedGammaPole n)) :=
    Summable.of_norm_bounded hsum (fun n => norm_integral_le_integral_norm _)
  apply (hi.mul_left (1 / (2 * (Real.pi : ℂ)))).congr
  intro n
  exact integral_finiteLaplace_sub_pole_mul_hadamardAtom hd hM hf hg hh hfg hgh
    hfd hg₀ hgd hbound hcs ((shiftedGammaPole_re_nonpos n).trans_lt hc)

/-- The actual smoothed shifted-digamma contour integrand is absolutely integrable. -/
theorem integrable_finiteLaplace_mul_digamma_half_add_one :
    Integrable (fun t : ℝ => (finiteLaplace f d (s - ((c : ℂ) + (t : ℂ) * I)) -
        f 0 / (s - ((c : ℂ) + (t : ℂ) * I))) *
      digamma (((c : ℂ) + (t : ℂ) * I) / 2 + 1)) := by
  have hC : 0 ≤ M / (s.re - c) * (1 + ‖s‖ / (s.re - c)) ^ 2 :=
    mul_nonneg (div_nonneg hM (sub_pos.mpr hcs).le) (sq_nonneg _)
  exact integrable_mul_digamma_half_add_one hc hC
    (integrable_finiteLaplace_sub_pole_contour hd hM hf hg hh hfg hgh hfd hg₀ hgd hbound hcs)
    (norm_finiteLaplace_sub_pole_contour_le hd hM hf hg hh hfg hgh hfd hg₀ hgd hbound hc hcs)

/-- The gamma part of the smoothed explicit formula equals the negative trivial-zero series. -/
theorem integral_finiteLaplace_mul_digamma_half_add_one_eq_remainders :
    (1 / (2 * (Real.pi : ℂ))) * (∫ t : ℝ,
      (finiteLaplace f d (s - ((c : ℂ) + (t : ℂ) * I)) -
        f 0 / (s - ((c : ℂ) + (t : ℂ) * I))) *
      digamma (((c : ℂ) + (t : ℂ) * I) / 2 + 1)) =
      -2 * ∑' n : ℕ, (finiteLaplace f d (s - shiftedGammaPole n) -
        f 0 / (s - shiftedGammaPole n)) := by
  have hC : 0 ≤ M / (s.re - c) * (1 + ‖s‖ / (s.re - c)) ^ 2 :=
    mul_nonneg (div_nonneg hM (sub_pos.mpr hcs).le) (sq_nonneg _)
  rw [integral_mul_digamma_half_add_one_eq_tsum hc hC
    (integrable_finiteLaplace_sub_pole_contour hd hM hf hg hh hfg hgh hfd hg₀ hgd hbound hcs)
    (norm_finiteLaplace_sub_pole_contour_le hd hM hf hg hh hfg hgh hfd hg₀ hgd hbound hc hcs)
    (integral_finiteLaplace_sub_pole_contour_eq_zero hd hM hf hg hh hfg hgh
      hfd hg₀ hgd hbound hcs)]
  rw [mul_left_comm, ← tsum_mul_left]
  congr 1
  apply tsum_congr
  intro n
  exact integral_finiteLaplace_sub_pole_mul_hadamardAtom hd hM hf hg hh hfg hgh
    hfd hg₀ hgd hbound hcs ((shiftedGammaPole_re_nonpos n).trans_lt hc)

end

end PrimeFactorUnimodality
