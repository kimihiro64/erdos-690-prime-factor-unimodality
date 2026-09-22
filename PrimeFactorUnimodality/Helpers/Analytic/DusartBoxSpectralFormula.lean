import PrimeFactorUnimodality.Helpers.Analytic.DusartBoxAverageFormula
import PrimeFactorUnimodality.Helpers.Analytic.DusartBoxMainTerm
import PrimeFactorUnimodality.Helpers.Analytic.DusartBoxZeroBounds

/-! # The averaged psi error after evaluating the main and spectral terms

The complete xi series is expressed in the actual averaged powers, with
each analytic multiplicity retained. Finite selections inherit the BV
zero-free damping bound. The negative-even series and constant are kept
explicit; they are not dropped from the Chebyshev error.
-/

namespace PrimeFactorUnimodality

noncomputable section

open Complex intervalIntegral

theorem smoothedXiPairedSum_box_eq_power_average (m : ℕ) {h x : ℝ}
    (hh : 0 < h) (hx : 1 < x) :
    smoothedXiPairedSum (fun u => (dusartBoxWeight m h x u : ℂ)) (dusartBoxSupport m h x) 0 =
      ∑' p : RiemannXiDivisorZeroIndex,
        iteratedBoxAverageComplex h (m + 3)
          (fun t => (t : ℂ) ^ riemannXiDivisorZeroValue p / riemannXiDivisorZeroValue p) x := by
  unfold smoothedXiPairedSum
  apply tsum_congr
  intro p
  simp only [zero_sub, dusartBoxWeight_zero m hh hx.le, ofReal_one]
  exact finiteLaplace_dusartBoxWeight_add_inv m hh hx (riemannXiDivisorZeroValue_ne_zero p)

theorem norm_sum_dusartBox_xi_power_average_le (m : ℕ) {h x δ : ℝ}
    (hh : 0 < h) (hx : 1 < x) (hδ : 0 ≤ δ) (S : Finset RiemannXiDivisorZeroIndex)
    (hgap : ∀ p ∈ S, (riemannXiDivisorZeroValue p).re ≤ 1 - δ) :
    ‖∑ p ∈ S, iteratedBoxAverageComplex h (m + 3)
        (fun t => (t : ℂ) ^ riemannXiDivisorZeroValue p / riemannXiDivisorZeroValue p) x‖ ≤
      ((x + (m + 3 : ℕ) * h) * Real.exp (-δ * Real.log x)) *
        ∑ p ∈ S, ‖(1 : ℂ) / riemannXiDivisorZeroValue p‖ := by
  refine (norm_sum_le _ _).trans ?_
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro p hp
  rw [← finiteLaplace_dusartBoxWeight_add_inv m hh hx (riemannXiDivisorZeroValue_ne_zero p)]
  exact norm_dusartBox_paired_atom_le m hh hx hδ (riemannXiDivisorZeroValue_ne_zero p) (hgap p hp)

/-- The actual averaged powers are absolutely summable over all xi zeros. -/
theorem summable_dusartBox_xi_power_average (m : ℕ) {h x : ℝ}
    (hh : 0 < h) (hx : 1 < x) :
    Summable (fun p : RiemannXiDivisorZeroIndex =>
      iteratedBoxAverageComplex h (m + 3)
        (fun t => (t : ℂ) ^ riemannXiDivisorZeroValue p / riemannXiDivisorZeroValue p) x) := by
  have hc := contDiff_dusartBoxWeight m hh x
  have hd : ContDiff ℝ 1 (deriv (dusartBoxWeight m h x)) := hc.deriv'
  have he := hd.continuous_deriv (by norm_num)
  have hs := dusartBoxSupport_pos m hh hx
  have hx0 : 0 < x := lt_trans zero_lt_one hx
  obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn he.continuousOn
    (s := Set.Icc 0 (dusartBoxSupport m h x))
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0 ⟨le_rfl, hs.le⟩)
  have ha := summable_smoothedXiPaired
    (f := fun u => (dusartBoxWeight m h x u : ℂ))
    (g := fun u => Complex.ofReal (deriv (dusartBoxWeight m h x) u))
    (h := fun u => Complex.ofReal (deriv (deriv (dusartBoxWeight m h x)) u))
    hs.le hM0 (Complex.continuous_ofReal.comp hc.continuous).continuousOn
    (Complex.continuous_ofReal.comp hd.continuous).continuousOn
    (Complex.continuous_ofReal.comp he).continuousOn
    (fun u _ => ((hc.differentiable (by norm_num)) u).hasDerivAt.ofReal_comp)
    (fun u _ => ((hd.differentiable (by norm_num)) u).hasDerivAt.ofReal_comp)
    (by simp [dusartBoxWeight_eq_zero m hh hx0 le_rfl])
    (by simp [deriv_dusartBoxWeight_zero m hh hx.le])
    (by simp [deriv_dusartBoxWeight_support m hh hx0])
    (fun u hu => by simpa only [Complex.norm_real] using hM u hu) 0
  apply ha.congr
  intro p
  simp only [zero_sub, dusartBoxWeight_zero m hh hx.le, ofReal_one]
  exact finiteLaplace_dusartBoxWeight_add_inv m hh hx (riemannXiDivisorZeroValue_ne_zero p)

/-- The true psi error with its main term cancelled and its complete zero series retained. -/
theorem dusartPsiAverageError_eq_spectral (m : ℕ) {h x : ℝ}
    (hh : 0 < h) (hx : 1 < x) :
    (dusartPsiAverageError (m + 3) h x : ℂ) =
      -(∑' p : RiemannXiDivisorZeroIndex,
        iteratedBoxAverageComplex h (m + 3)
          (fun t => (t : ℂ) ^ riemannXiDivisorZeroValue p / riemannXiDivisorZeroValue p) x) -
        smoothedGammaPairedSum (fun u => (dusartBoxWeight m h x u : ℂ))
          (dusartBoxSupport m h x) 0 -
        (logDeriv riemannXi 0 +
          ((Real.log Real.pi : ℂ) + Real.eulerMascheroniConstant) / 2) - 1 := by
  rw [dusartPsiAverageError_box_explicitFormula m hh hx,
    finiteLaplace_dusartBoxWeight_neg_one m hh hx,
    smoothedXiPairedSum_box_eq_power_average m hh hx]
  ring

end

end PrimeFactorUnimodality
