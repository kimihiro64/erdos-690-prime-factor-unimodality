import PrimeFactorUnimodality.Helpers.Analytic.XiHeightBand
import PrimeFactorUnimodality.Helpers.Analytic.XiRosserIncreasingBound

/-! # Both ordinate signs in the finite increasing Rosser band

The existing band-cover argument is used for a general nonnegative
conjugation-invariant weight. The lower window cutoff is halved so that
zeros exactly at the band's lower boundary are retained. No new indexing
or zero-location assumption is needed for the weighted counting bound.
-/

namespace PrimeFactorUnimodality

noncomputable section

open Complex Real

/-- Both signs, with exact zero cost for an empty band. -/
def xiRosserIncreasingBandBound (a H T : ℝ) : ℝ :=
  if H < T then 2 * xiRosserIncreasingBound a (H / 2) T else 0

@[simp] theorem xiRosserIncreasingBandBound_self (a H : ℝ) :
    xiRosserIncreasingBandBound a H H = 0 := by simp [xiRosserIncreasingBandBound]

/-- Conjugation reduces the actual absolute-height kernel sum to a positive window. -/
theorem sum_xi_band_logDampedPower_le_twice_window {a q H T : ℝ} (hH : 0 < H) :
    (∑ p ∈ xiHeightBandIndices H T, logDampedPower a q |(riemannXiDivisorZeroValue p).im|) ≤
      2 * ∑ p ∈ xiHeightWindowIndices (H / 2) T,
        logDampedPower a q (riemannXiDivisorZeroValue p).im := by
  have hs := sum_xi_band_le_twice_window (b := T) hH
    (f := fun p => logDampedPower a q |(riemannXiDivisorZeroValue p).im|)
    (fun _ => (logDampedPower_pos _ _ _).le)
    (fun p => by simp only [riemannXiDivisorZeroValue_conjugation, conj_im, abs_neg])
  refine hs.trans_eq ?_
  congr 1
  apply Finset.sum_congr rfl
  intro p hp
  rw [abs_of_pos ((mem_xiHeightWindowIndices (H / 2) T p).mp hp).1.1]

/-- The finite two-sided exponent-one band has a closed endpoint bound. -/
theorem sum_xi_band_logDampedPower_one_le_increasing {a H T : ℝ}
    (ha : 0 < a) (hH : 20 ≤ H) (hHT : H ≤ T) (hT : T ≤ exp (sqrt a)) :
    (∑ p ∈ xiHeightBandIndices H T, logDampedPower a 1 |(riemannXiDivisorZeroValue p).im|) ≤
      xiRosserIncreasingBandBound a H T := by
  rcases hHT.eq_or_lt with rfl | hHT'
  · simp
  rw [xiRosserIncreasingBandBound, ite_eq_left hHT']
  exact (sum_xi_band_logDampedPower_le_twice_window (by linarith : 0 < H)).trans
    (mul_le_mul_of_nonneg_left (sum_xi_logDampedPower_one_le_increasing ha
      (by linarith) (by linarith) hT) (by norm_num))

end

end PrimeFactorUnimodality
