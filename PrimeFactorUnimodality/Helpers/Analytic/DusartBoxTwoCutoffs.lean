import PrimeFactorUnimodality.Helpers.Analytic.DusartBoxZeroSplit
import PrimeFactorUnimodality.Helpers.Analytic.XiHeightBandGap
import PrimeFactorUnimodality.Helpers.Analytic.XiLowReciprocalNormBound

/-! # Separate low, intermediate, and high xi zeros in the Dusart box estimate

A fixed low-height gap is used only below `H`. The intermediate band
`[H,T)` uses the proved initial region, while the closed tail at `T` uses
the complete higher-order decay estimate. Counting supplies both finite
reciprocal-norm masses. In particular the strong low gap need not extend
to the variable high cutoff.
-/

namespace PrimeFactorUnimodality

noncomputable section

open Complex intervalIntegral

/-- Exact three-way split, including all labels on either cutoff. -/
theorem smoothedXiPairedSum_box_eq_low_add_band_add_high (m : ℕ) {h x H T : ℝ}
    (hh : 0 < h) (hx : 1 < x) (hHT : H ≤ T) :
    smoothedXiPairedSum (fun u => (dusartBoxWeight m h x u : ℂ)) (dusartBoxSupport m h x) 0 =
      (∑ p ∈ xiLowHeightIndices H, iteratedBoxAverageComplex h (m + 3)
        (fun t => (t : ℂ) ^ riemannXiDivisorZeroValue p / riemannXiDivisorZeroValue p) x) +
      (∑ p ∈ xiHeightBandIndices H T, iteratedBoxAverageComplex h (m + 3)
        (fun t => (t : ℂ) ^ riemannXiDivisorZeroValue p / riemannXiDivisorZeroValue p) x) +
        dusartBoxXiHighSum m h x T := by
  classical
  let : DecidableEq RiemannXiDivisorZeroIndex := Classical.decEq _
  have hs := Finset.sum_union
    (f := fun p => iteratedBoxAverageComplex h (m + 3)
      (fun t => (t : ℂ) ^ riemannXiDivisorZeroValue p / riemannXiDivisorZeroValue p) x)
    (disjoint_xiLowHeightIndices_band H T)
  rw [xiLowHeightIndices_union_band hHT] at hs
  rw [smoothedXiPairedSum_box_eq_low_add_high m hh hx T, hs]

/-- Independent damping for the fixed low prefix and the variable intermediate band. -/
def dusartBoxTwoCutoffZeroBudget (m : ℕ) (h x a H T δ : ℝ) : ℝ :=
  ((x + (m + 3 : ℕ) * h) * Real.exp (-δ * Real.log x)) *
      xiLowReciprocalNormBound a H δ +
    ((x + (m + 3 : ℕ) * h) * Real.exp (-(1 / (56 * Real.log T)) * Real.log x)) *
      xiBandReciprocalNormBound H T +
    dusartBoxTailFactor m h x T * (4 * xiLehmanHighBound (T / 2) (T / 2))

/-- The actual entire xi series is bounded with a location input only below the fixed cutoff. -/
theorem norm_smoothedXiPairedSum_box_le_two_cutoffs (m : ℕ) {h x a H T δ : ℝ}
    (hh : 0 < h) (hx : 1 < x) (ha : 10 ≤ a) (haH : a < H)
    (hH : 10 ^ 9 ≤ H) (hHT : H ≤ T) (hδ : 0 < δ)
    (hgap : ∀ p ∈ xiLowHeightIndices H, (riemannXiDivisorZeroValue p).re ≤ 1 - δ) :
    ‖smoothedXiPairedSum (fun u => (dusartBoxWeight m h x u : ℂ))
        (dusartBoxSupport m h x) 0‖ ≤ dusartBoxTwoCutoffZeroBudget m h x a H T δ := by
  have hT := hH.trans hHT
  have hx0 : 0 < x := lt_trans zero_lt_one hx
  have hlow := norm_sum_dusartBox_xi_power_average_le m hh hx hδ.le _ hgap
  have hmid := norm_sum_dusartBox_xi_power_average_le m hh hx
    (xi_initial_gap_pos hT).le (xiHeightBandIndices H T)
    (fun _ hp => xi_height_band_re_le_initial_gap hH hp)
  have hlow' := hlow.trans (mul_le_mul_of_nonneg_left
    (sum_xi_low_reciprocal_norm_le_explicit ha haH hδ hgap) (by positivity))
  have hmid' := hmid.trans (mul_le_mul_of_nonneg_left
    (sum_xi_band_reciprocal_norm_le_bound (by linarith : 20 ≤ H) hHT) (by positivity))
  rw [smoothedXiPairedSum_box_eq_low_add_band_add_high m hh hx hHT]
  exact (norm_add_le _ _).trans (add_le_add
    ((norm_add_le _ _).trans (add_le_add hlow' hmid'))
    (norm_dusartBoxXiHighSum_le_highBound m hh hx hT))

end

end PrimeFactorUnimodality
