import PrimeFactorUnimodality.Helpers.Analytic.SmoothedPairedSums

/-! # Converting regularized resolvents into entire paired Laplace sums

Absolute summability permits termwise subtraction of the genus-one
resolvent series. The xi and digamma expansions then identify the pole
corrections explicitly. These identities connect contour evaluation with
the entire functions used for analytic continuation.
-/

namespace PrimeFactorUnimodality

noncomputable section

open Complex Set

variable {f g h : ℝ → ℂ} {d M : ℝ}
  (hd : 0 ≤ d) (hM : 0 ≤ M)
  (hf : ContinuousOn f (Icc 0 d)) (hg : ContinuousOn g (Icc 0 d))
  (hh : ContinuousOn h (Icc 0 d))
  (hfg : ∀ t ∈ Ioo 0 d, HasDerivAt f (g t) t)
  (hgh : ∀ t ∈ Ioo 0 d, HasDerivAt g (h t) t)
  (hfd : f d = 0) (hg₀ : g 0 = 0) (hgd : g d = 0)
  (hbound : ∀ t ∈ Icc 0 d, ‖h t‖ ≤ M)

include hd hM hf hg hh hfg hgh hfd hg₀ hgd hbound

/-- The xi pole corrections combine into its logarithmic derivative minus the constant. -/
theorem smoothedXiPairedSum_sub_logDeriv_eq_remainders {s : ℂ} (hs : riemannXi s ≠ 0) :
    smoothedXiPairedSum f d s - f 0 * (logDeriv riemannXi s - logDeriv riemannXi 0) =
      ∑' p : RiemannXiDivisorZeroIndex,
        (finiteLaplace f d (s - riemannXiDivisorZeroValue p) -
          f 0 / (s - riemannXiDivisorZeroValue p)) := by
  have hpair := summable_smoothedXiPaired hd hM hf hg hh hfg hgh hfd hg₀ hgd hbound s
  have hatom := summable_riemannXi_logDerivTerms_divisorZeroIndex₀ (z := s)
    (fun p heq => hs (heq ▸ riemannXiDivisorZeroValue_eq_zero p))
  rw [logDeriv_riemannXi_eq_zero_add_tsum_of_ne_zero hs, add_sub_cancel_left,
    smoothedXiPairedSum, ← tsum_mul_left, ← hpair.tsum_sub (hatom.mul_left (f 0))]
  apply tsum_congr
  intro p
  ring

/-- The gamma pole corrections combine into the digamma value and Euler's constant. -/
theorem smoothedGammaPairedSum_add_digamma_eq_remainders {s : ℂ} (hs : 0 < s.re) :
    smoothedGammaPairedSum f d s + f 0 / 2 *
      (digamma (s / 2 + 1) + (Real.eulerMascheroniConstant : ℂ)) =
      ∑' n : ℕ, (finiteLaplace f d (s - shiftedGammaPole n) - f 0 / (s - shiftedGammaPole n)) := by
  have hpair := summable_smoothedGammaPaired hd hM hf hg hh hfg hgh hfd hg₀ hgd hbound s
  have hatom := summable_shiftedGamma_atoms hs
  have heq : smoothedGammaPairedSum f d s - f 0 *
      (∑' n : ℕ, (1 / (s - shiftedGammaPole n) + 1 / shiftedGammaPole n)) =
      ∑' n : ℕ, (finiteLaplace f d (s - shiftedGammaPole n) - f 0 / (s - shiftedGammaPole n)) := by
    rw [smoothedGammaPairedSum, ← tsum_mul_left, ← hpair.tsum_sub (hatom.mul_left (f 0))]
    apply tsum_congr
    intro n
    ring
  rw [digamma_half_add_one_eq_shiftedGamma_tsum hs]
  linear_combination heq

end

end PrimeFactorUnimodality
