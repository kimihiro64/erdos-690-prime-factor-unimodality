import PrimeFactorUnimodality.Helpers.Analytic.DusartBoxHighTail

/-! # Exact low/high split of the box-smoothed xi series

The finite low set uses a strict height cutoff, while the high set is
closed. Absolute summability justifies the split. Combining the existing
finite damping bound with the new complete high-tail estimate leaves only
the explicitly stated low-height location and reciprocal-mass inputs.
-/

namespace PrimeFactorUnimodality

noncomputable section

open Complex intervalIntegral

theorem smoothedXiPairedSum_box_eq_low_add_high (m : ℕ) {h x : ℝ}
    (hh : 0 < h) (hx : 1 < x) (T : ℝ) :
    smoothedXiPairedSum (fun u => (dusartBoxWeight m h x u : ℂ)) (dusartBoxSupport m h x) 0 =
      (∑ p ∈ xiLowHeightIndices T, iteratedBoxAverageComplex h (m + 3)
        (fun t => (t : ℂ) ^ riemannXiDivisorZeroValue p / riemannXiDivisorZeroValue p) x) +
        dusartBoxXiHighSum m h x T := by
  rw [smoothedXiPairedSum_box_eq_power_average m hh hx]
  have he := (summable_dusartBox_xi_power_average m hh hx).sum_add_tsum_subtype_compl
    (xiLowHeightIndices T)
  have hpred : (fun p : RiemannXiDivisorZeroIndex => p ∉ xiLowHeightIndices T) =
      (fun p => T ≤ |(riemannXiDivisorZeroValue p).im|) := by
    funext p
    simp only [mem_xiLowHeightIndices, not_lt]
  rw [hpred] at he
  exact he.symm

/-- The full actual zero sum has an explicit bound given its finite low-height gap. -/
theorem norm_smoothedXiPairedSum_box_le_low_gap_add_high (m : ℕ) {h x T δ : ℝ}
    (hh : 0 < h) (hx : 1 < x) (hT : 10 ^ 9 ≤ T) (hδ : 0 ≤ δ)
    (hgap : ∀ p ∈ xiLowHeightIndices T, (riemannXiDivisorZeroValue p).re ≤ 1 - δ) :
    ‖smoothedXiPairedSum (fun u => (dusartBoxWeight m h x u : ℂ))
        (dusartBoxSupport m h x) 0‖ ≤
      ((x + (m + 3 : ℕ) * h) * Real.exp (-δ * Real.log x)) *
        (∑ p ∈ xiLowHeightIndices T, ‖(1 : ℂ) / riemannXiDivisorZeroValue p‖) +
      dusartBoxTailFactor m h x T * (4 * xiLehmanHighBound (T / 2) (T / 2)) := by
  rw [smoothedXiPairedSum_box_eq_low_add_high m hh hx T]
  exact (norm_add_le _ _).trans
    (add_le_add (norm_sum_dusartBox_xi_power_average_le m hh hx hδ _ hgap)
      (norm_dusartBoxXiHighSum_le_highBound m hh hx hT))

end

end PrimeFactorUnimodality
