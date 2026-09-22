import PrimeFactorUnimodality.Helpers.Analytic.XiHadamardIntegral
import PrimeFactorUnimodality.Mathlib.Analysis.Complex.FiniteLaplace.ResolventIntegral

/-! # Integrating the xi expansion against the actual smoothing weight

The finite Laplace endpoint conditions supply both the quadratic contour
majorant and the vanishing integral needed by the Hadamard interchange.
Every actual xi zero is retained with its divisor multiplicity. Neither
an assumed interchange nor a bound for an unspecified contour weight is
required by these theorems.
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
  {s : ℂ} {c : ℝ} (hc : 1 < c) (hcs : c < s.re)

include hd hM hf hg hh hfg hgh hfd hg₀ hgd hbound hc hcs

/-- The actual pole-subtracted Laplace weight satisfies absolute xi-series Fubini. -/
theorem summable_integral_norm_finiteLaplace_xi_atoms :
    Summable (fun p : RiemannXiDivisorZeroIndex => ∫ t : ℝ,
      ‖(finiteLaplace f d (s - ((c : ℂ) + (t : ℂ) * I)) -
          f 0 / (s - ((c : ℂ) + (t : ℂ) * I))) *
        (1 / ((c : ℂ) + (t : ℂ) * I - riemannXiDivisorZeroValue p) +
          1 / riemannXiDivisorZeroValue p)‖) := by
  have hC : 0 ≤ M / (s.re - c) * (1 + ‖s‖ / (s.re - c)) ^ 2 :=
    mul_nonneg (div_nonneg hM (sub_pos.mpr hcs).le) (sq_nonneg _)
  exact summable_integral_norm_mul_xi_hadamardAtoms hc hC
    (integrable_finiteLaplace_sub_pole_contour hd hM hf hg hh hfg hgh hfd hg₀ hgd hbound hcs)
    (norm_finiteLaplace_sub_pole_contour_le hd hM hf hg hh hfg hgh hfd hg₀ hgd hbound
      (by linarith) hcs)

/-- The smoothed xi contour integral equals the whole integrated zero series. -/
theorem integral_finiteLaplace_mul_logDeriv_riemannXi_eq_tsum :
    (∫ t : ℝ, (finiteLaplace f d (s - ((c : ℂ) + (t : ℂ) * I)) -
        f 0 / (s - ((c : ℂ) + (t : ℂ) * I))) *
      logDeriv riemannXi ((c : ℂ) + (t : ℂ) * I)) =
      ∑' p : RiemannXiDivisorZeroIndex, ∫ t : ℝ,
        (finiteLaplace f d (s - ((c : ℂ) + (t : ℂ) * I)) -
          f 0 / (s - ((c : ℂ) + (t : ℂ) * I))) *
        (1 / ((c : ℂ) + (t : ℂ) * I - riemannXiDivisorZeroValue p) +
          1 / riemannXiDivisorZeroValue p) := by
  have hC : 0 ≤ M / (s.re - c) * (1 + ‖s‖ / (s.re - c)) ^ 2 :=
    mul_nonneg (div_nonneg hM (sub_pos.mpr hcs).le) (sq_nonneg _)
  exact integral_mul_logDeriv_riemannXi_eq_tsum hc hC
    (integrable_finiteLaplace_sub_pole_contour hd hM hf hg hh hfg hgh hfd hg₀ hgd hbound hcs)
    (norm_finiteLaplace_sub_pole_contour_le hd hM hf hg hh hfg hgh hfd hg₀ hgd hbound
      (by linarith) hcs)
    (integral_finiteLaplace_sub_pole_contour_eq_zero hd hM hf hg hh hfg hgh
      hfd hg₀ hgd hbound hcs)

/-- The evaluated xi contour identity, summed over the actual divisor with multiplicities. -/
theorem integral_finiteLaplace_mul_logDeriv_riemannXi_eq_remainders :
    (1 / (2 * (Real.pi : ℂ))) * (∫ t : ℝ,
      (finiteLaplace f d (s - ((c : ℂ) + (t : ℂ) * I)) -
        f 0 / (s - ((c : ℂ) + (t : ℂ) * I))) *
      logDeriv riemannXi ((c : ℂ) + (t : ℂ) * I)) =
      ∑' p : RiemannXiDivisorZeroIndex,
        (finiteLaplace f d (s - riemannXiDivisorZeroValue p) -
          f 0 / (s - riemannXiDivisorZeroValue p)) := by
  rw [integral_finiteLaplace_mul_logDeriv_riemannXi_eq_tsum hd hM hf hg hh hfg hgh
    hfd hg₀ hgd hbound hc hcs, ← tsum_mul_left]
  apply tsum_congr
  intro p
  exact integral_finiteLaplace_sub_pole_mul_hadamardAtom hd hM hf hg hh hfg hgh
    hfd hg₀ hgd hbound hcs
    ((riemannXi_zero_mem_critical_strip (riemannXiDivisorZeroValue_eq_zero p)).2.trans_lt hc)

end

end PrimeFactorUnimodality
