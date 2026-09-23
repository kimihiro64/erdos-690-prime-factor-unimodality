import PrimeFactorUnimodality.Helpers.Analytic.XiLehmanBudget

/-! # An explicit high-cutoff bound for the zero-height xi tail

Shift the evaluation height to half the cutoff. The same closed set of
zeros is retained, and each zero-height inverse square is at most four
times its shifted value. The proved high Lehman bound then supplies an
explicit estimate without any finite low-zero mass input.
-/

namespace PrimeFactorUnimodality

noncomputable section

open Complex Real

theorem xiHeightTail_zero_eq_tsum (T : ℝ) :
    xiHeightTail 0 T = ∑' p : {p : RiemannXiDivisorZeroIndex //
      T ≤ |(riemannXiDivisorZeroValue p).im|}, 1 / (riemannXiDivisorZeroValue p.1).im ^ 2 := by
  have he : (fun p : RiemannXiDivisorZeroIndex => |(0 : ℝ)| + T ≤
      |(riemannXiDivisorZeroValue p).im|) = (fun p => T ≤ |(riemannXiDivisorZeroValue p).im|) := by
    funext p
    simp
  rw [xiHeightTail, he]
  simp only [zero_sub, neg_sq]

private theorem zero_inv_sq_le_half_shift {T γ : ℝ} (hT : 0 < T) (hγ : T ≤ |γ|) :
    1 / γ ^ 2 ≤ 4 * (1 / (T / 2 - γ) ^ 2) := by
  have ht : 0 < T / 2 := by linarith
  have hg : γ ≠ 0 := abs_pos.mp (hT.trans_le hγ)
  have hcut : |T / 2| + T / 2 ≤ |γ| := by rw [abs_of_pos ht]; linarith
  have hsep := sq_le_sub_sq_of_abs_cutoff ht.le hcut
  have hd : 0 < (T / 2 - γ) ^ 2 := (sq_pos_of_pos ht).trans_le hsep
  have hab : |T / 2 - γ| ≤ 2 * |γ| := by
    have he := abs_sub (T / 2) γ
    rw [abs_of_pos ht] at he
    linarith
  have hsq : (T / 2 - γ) ^ 2 ≤ 4 * γ ^ 2 := by
    have he := mul_nonneg (sub_nonneg.mpr hab)
      (add_nonneg (by positivity : 0 ≤ 2 * |γ|) (abs_nonneg (T / 2 - γ)))
    nlinarith [sq_abs γ, sq_abs (T / 2 - γ)]
  rw [mul_one_div]
  exact (div_le_div_iff₀ (sq_pos_of_ne_zero hg) hd).mpr (by simpa using hsq)

theorem xiHeightTail_zero_le_half_shift {T : ℝ} (hT : 0 < T) :
    xiHeightTail 0 T ≤ 4 * xiHeightTail (T / 2) (T / 2) := by
  have ht : 0 < T / 2 := by linarith
  have he : T / 2 + T / 2 = T := by ring
  have hpred0 : (fun p : RiemannXiDivisorZeroIndex => |(0 : ℝ)| + T ≤
      |(riemannXiDivisorZeroValue p).im|) = (fun p => T ≤ |(riemannXiDivisorZeroValue p).im|) := by
    funext p
    simp
  have hpred1 : (fun p : RiemannXiDivisorZeroIndex => |T / 2| + T / 2 ≤
      |(riemannXiDivisorZeroValue p).im|) = (fun p => T ≤ |(riemannXiDivisorZeroValue p).im|) := by
    funext p
    rw [abs_of_pos ht, he]
  have hs0 := summable_xiHeightTail hT 0
  rw [hpred0] at hs0
  have hs1 : Summable (fun p : {p : RiemannXiDivisorZeroIndex //
      T ≤ |(riemannXiDivisorZeroValue p).im|} =>
      1 / (T / 2 - (riemannXiDivisorZeroValue p.1).im) ^ 2) :=
    summable_xi_height_inv_sq ht (T / 2) (fun p hp =>
      sq_le_sub_sq_of_abs_cutoff ht.le (by rw [abs_of_pos ht, he]; exact hp))
  simp only [zero_sub, neg_sq] at hs0
  rw [xiHeightTail_zero_eq_tsum, xiHeightTail, hpred1]
  rw [← tsum_mul_left]
  exact hs0.tsum_le_tsum (fun p => zero_inv_sq_le_half_shift hT p.2) (hs1.mul_left 4)

theorem xiHeightTail_zero_le_highBound {T : ℝ} (hT : 10 ^ 9 ≤ T) :
    xiHeightTail 0 T ≤ 4 * xiLehmanHighBound (T / 2) (T / 2) := by
  have ht : 0 < T / 2 := by linarith
  exact (xiHeightTail_zero_le_half_shift (by linarith)).trans
    (mul_le_mul_of_nonneg_left
      (xiHeightTail_le_highBound ht ht (by linarith)) (by norm_num))

end

end PrimeFactorUnimodality
