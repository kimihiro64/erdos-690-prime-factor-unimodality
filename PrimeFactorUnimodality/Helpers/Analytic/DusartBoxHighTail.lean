import PrimeFactorUnimodality.Helpers.Analytic.DusartBoxHeightDecay
import PrimeFactorUnimodality.Helpers.Analytic.DusartBoxSpectralFormula
import PrimeFactorUnimodality.Helpers.Analytic.XiHeightTailZeroHigh

/-! # Quantitative control of the complete high-zero box tail

The higher-order atom estimate is summed over the actual closed absolute
height cutoff, including every multiplicity and both ordinate signs.
The existing Lehman theorem supplies a fully explicit high-cutoff bound.
This does not supply the remaining low-zero contribution.
-/

namespace PrimeFactorUnimodality

noncomputable section

open Complex Real intervalIntegral

def dusartBoxXiHighSum (m : ℕ) (h x T : ℝ) : ℂ :=
  ∑' p : {p : RiemannXiDivisorZeroIndex // T ≤ |(riemannXiDivisorZeroValue p).im|},
    iteratedBoxAverageComplex h (m + 3)
      (fun t => (t : ℂ) ^ riemannXiDivisorZeroValue p.1 / riemannXiDivisorZeroValue p.1) x

theorem dusartBoxTailFactor_nonneg (m : ℕ) {h x T : ℝ}
    (hh : 0 < h) (hx : 1 < x) (hT : 0 < T) : 0 ≤ dusartBoxTailFactor m h x T := by
  unfold dusartBoxTailFactor
  have hx0 : 0 < x := lt_trans zero_lt_one hx
  positivity

theorem norm_dusartBoxXiHighSum_le_heightTail (m : ℕ) {h x T : ℝ}
    (hh : 0 < h) (hx : 1 < x) (hT : 0 < T) :
    ‖dusartBoxXiHighSum m h x T‖ ≤ dusartBoxTailFactor m h x T * xiHeightTail 0 T := by
  let P : RiemannXiDivisorZeroIndex → Prop := fun p => T ≤ |(riemannXiDivisorZeroValue p).im|
  have ha := ((summable_dusartBox_xi_power_average m hh hx).subtype P).norm
  have hb := (summable_xiHeightTail hT 0).mul_left (dusartBoxTailFactor m h x T)
  have hpred0 : (fun p : RiemannXiDivisorZeroIndex => |(0 : ℝ)| + T ≤
      |(riemannXiDivisorZeroValue p).im|) = P := by funext p; simp [P]
  rw [hpred0] at hb
  simp only [zero_sub, neg_sq] at hb
  have hp (p : {p : RiemannXiDivisorZeroIndex // P p}) :
      ‖iteratedBoxAverageComplex h (m + 3)
        (fun t => (t : ℂ) ^ riemannXiDivisorZeroValue p.1 / riemannXiDivisorZeroValue p.1) x‖ ≤
        dusartBoxTailFactor m h x T * (1 / (riemannXiDivisorZeroValue p.1).im ^ 2) := by
    rw [← finiteLaplace_dusartBoxWeight_add_inv m hh hx (riemannXiDivisorZeroValue_ne_zero p.1)]
    obtain ⟨hl, hu⟩ := riemannXi_zero_mem_critical_strip (riemannXiDivisorZeroValue_eq_zero p.1)
    exact norm_dusartBox_paired_atom_le_tail_kernel m hh hx hT hl hu p.2
  calc
    ‖dusartBoxXiHighSum m h x T‖ ≤ _ := norm_tsum_le_tsum_norm ha
    _ ≤ ∑' p : {p : RiemannXiDivisorZeroIndex // P p},
        dusartBoxTailFactor m h x T * (1 / (riemannXiDivisorZeroValue p.1).im ^ 2) :=
      ha.tsum_le_tsum hp hb
    _ = dusartBoxTailFactor m h x T * xiHeightTail 0 T := by
      rw [tsum_mul_left]
      rw [xiHeightTail_zero_eq_tsum]

/-- The whole high tail has an explicit bound once the proved counting cutoff applies. -/
theorem norm_dusartBoxXiHighSum_le_highBound (m : ℕ) {h x T : ℝ}
    (hh : 0 < h) (hx : 1 < x) (hT : 10 ^ 9 ≤ T) :
    ‖dusartBoxXiHighSum m h x T‖ ≤
      dusartBoxTailFactor m h x T * (4 * xiLehmanHighBound (T / 2) (T / 2)) :=
  (norm_dusartBoxXiHighSum_le_heightTail m hh hx (by linarith)).trans
    (mul_le_mul_of_nonneg_left (xiHeightTail_zero_le_highBound hT)
      (dusartBoxTailFactor_nonneg m hh hx (by linarith)))

end

end PrimeFactorUnimodality
