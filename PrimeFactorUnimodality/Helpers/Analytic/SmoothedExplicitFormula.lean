import PrimeFactorUnimodality.Helpers.Analytic.SmoothedDigammaIntegral
import PrimeFactorUnimodality.Helpers.Analytic.SmoothedPrimeIntegral
import PrimeFactorUnimodality.Helpers.Analytic.SmoothedXiInterchange
import PrimeFactorUnimodality.Helpers.Analytic.ZetaContourDecomposition

/-! # The smoothed explicit formula on the right half-plane

Absolute inversion identifies the prime side, Hadamard interchange
evaluates every nontrivial zero with its actual multiplicity, and the
digamma series evaluates the negative even poles. Their combination gives
the full regularized identity for every `Re(s)>1`, with no contour or
explicit-formula hypothesis. Extension below one and identification with
the half-line gamma remainder are separate analytic obligations.
-/

namespace PrimeFactorUnimodality

noncomputable section

open Complex MeasureTheory Set

/-- The pole-subtracted explicit formula with complete nontrivial and trivial zero sums. -/
theorem smoothedVonMangoldt_explicitFormula_of_one_lt_re
    {f : ℝ → ℝ} {g h : ℝ → ℂ} {d M : ℝ}
    (hd : 0 ≤ d) (hM : 0 ≤ M)
    (hf : ContinuousOn f (Icc 0 d)) (hg : ContinuousOn g (Icc 0 d))
    (hh : ContinuousOn h (Icc 0 d))
    (hfg : ∀ u ∈ Ioo 0 d, HasDerivAt (fun u => (f u : ℂ)) (g u) u)
    (hgh : ∀ u ∈ Ioo 0 d, HasDerivAt g (h u) u)
    (hfd : f d = 0) (hg₀ : g 0 = 0) (hgd : g d = 0)
    (hbound : ∀ u ∈ Icc 0 d, ‖h u‖ ≤ M) (htail : ∀ u, d < u → f u = 0)
    {s : ℂ} (hs : 1 < s.re) :
    smoothedVonMangoldt f s - (f 0 : ℂ) * (-deriv riemannZeta s / riemannZeta s) =
      (finiteLaplace (fun u => (f u : ℂ)) d (s - 1) - (f 0 : ℂ) / (s - 1)) -
      (∑' p : RiemannXiDivisorZeroIndex,
        (finiteLaplace (fun u => (f u : ℂ)) d (s - riemannXiDivisorZeroValue p) -
          (f 0 : ℂ) / (s - riemannXiDivisorZeroValue p))) -
      ∑' n : ℕ, (finiteLaplace (fun u => (f u : ℂ)) d (s - shiftedGammaPole n) -
        (f 0 : ℂ) / (s - shiftedGammaPole n)) := by
  let c : ℝ := (1 + s.re) / 2
  have hc : 1 < c := by dsimp [c]; linarith
  have hc₀ : 0 < c := by linarith
  have hcs : c < s.re := by dsimp [c]; linarith
  have hfc : ContinuousOn (fun u => (f u : ℂ)) (Icc 0 d) :=
    Complex.continuous_ofReal.comp_continuousOn hf
  have hfdc : (f d : ℂ) = 0 := by rw [hfd]; rfl
  let H : ℝ → ℂ := fun t => finiteLaplace (fun u => (f u : ℂ)) d
      (s - ((c : ℂ) + (t : ℂ) * I)) - (f 0 : ℂ) / (s - ((c : ℂ) + (t : ℂ) * I))
  have hH : Integrable H := integrable_finiteLaplace_sub_pole_contour hd hM hfc hg hh
    hfg hgh hfdc hg₀ hgd hbound hcs
  have hC : 0 ≤ M / (s.re - c) * (1 + ‖s‖ / (s.re - c)) ^ 2 :=
    mul_nonneg (div_nonneg hM (sub_pos.mpr hcs).le) (sq_nonneg _)
  have hBound := norm_finiteLaplace_sub_pole_contour_le hd hM hfc hg hh
    hfg hgh hfdc hg₀ hgd hbound hc₀ hcs
  have hZero := integral_finiteLaplace_sub_pole_contour_eq_zero hd hM hfc hg hh
    hfg hgh hfdc hg₀ hgd hbound hcs
  have hdecomp := integral_mul_neg_logDeriv_riemannZeta_eq hc hC hH hBound hZero
  have hprime := smoothedVonMangoldt_sub_logDeriv_eq_integral hd hM hf hg hh
    hfg hgh hfd hg₀ hgd hbound htail hc hcs
  have hxi := integral_finiteLaplace_mul_logDeriv_riemannXi_eq_remainders hd hM hfc hg hh
    hfg hgh hfdc hg₀ hgd hbound hc hcs
  have hp := integral_finiteLaplace_sub_pole_div_vertical hd hM hfc hg hh
    hfg hgh hfdc hg₀ hgd hbound hcs (ρ := 1) (by simpa using hc)
  have hgamma := integral_finiteLaplace_mul_digamma_half_add_one_eq_remainders hd hM hfc hg hh
    hfg hgh hfdc hg₀ hgd hbound hc₀ hcs
  have hprime' : smoothedVonMangoldt f s - (f 0 : ℂ) *
      (-deriv riemannZeta s / riemannZeta s) = (1 / (2 * (Real.pi : ℂ))) *
      (∫ t : ℝ, H t * (-deriv riemannZeta ((c : ℂ) + (t : ℂ) * I) /
        riemannZeta ((c : ℂ) + (t : ℂ) * I))) := by
    rw [hprime]
    congr 1
    apply integral_congr_ae
    filter_upwards with t
    exact mul_comm _ _
  rw [hprime', hdecomp]
  change (1 / (2 * (Real.pi : ℂ))) * (∫ t : ℝ, H t *
    logDeriv riemannXi ((c : ℂ) + (t : ℂ) * I)) = _ at hxi
  change (1 / (2 * (Real.pi : ℂ))) * (∫ t : ℝ, H t / _) = _ at hp
  change (1 / (2 * (Real.pi : ℂ))) * (∫ t : ℝ, H t *
    digamma (((c : ℂ) + (t : ℂ) * I) / 2 + 1)) = _ at hgamma
  linear_combination -hxi + hp + (1 / 2 : ℂ) * hgamma

end

end PrimeFactorUnimodality
