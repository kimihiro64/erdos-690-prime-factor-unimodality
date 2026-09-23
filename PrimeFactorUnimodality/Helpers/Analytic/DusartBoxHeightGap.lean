import PrimeFactorUnimodality.Helpers.Analytic.DusartBoxHeightDecay
import PrimeFactorUnimodality.Helpers.Analytic.ZetaZeroFreeInitial

/-! # Retaining zero-free damping in the higher-order box estimate

The height estimate need not discard the real-part gap. Keeping it gives
both the higher primitive denominator and exponential damping in the same
bound. This is the atom estimate needed to sharpen the high tail by the
height-dependent zero-free region, rather than using the critical strip alone.
-/

namespace PrimeFactorUnimodality

noncomputable section

open Complex intervalIntegral

/-- Higher-order height decay and real-part damping hold simultaneously. -/
theorem norm_dusartBox_paired_atom_le_height_gap (m : ℕ) {h x δ : ℝ}
    (hh : 0 < h) (hx : 1 < x) (hδ : 0 ≤ δ) {s : ℂ} (hs : s.im ≠ 0)
    (hβ0 : 0 ≤ s.re) (hβ : s.re ≤ 1 - δ) :
    ‖finiteLaplace (fun u => (dusartBoxWeight m h x u : ℂ)) (dusartBoxSupport m h x) (-s) +
        1 / s‖ ≤
      (2 ^ (m + 3) * (x + (m + 3 : ℕ) * h) ^ (m + 4) /
        (h ^ (m + 3) * |s.im| ^ (m + 4))) * Real.exp (-δ * Real.log x) := by
  have hs0 : s ≠ 0 := fun he => hs (by simp [he])
  rw [finiteLaplace_dusartBoxWeight_add_inv m hh hx hs0]
  have he := norm_iteratedBoxAverageComplex_cpow_div_le_height hh
    (lt_trans zero_lt_one hx) hs hβ0 (m + 3)
  let U := x + (m + 3 : ℕ) * h
  have hxU : x ≤ U := le_add_of_nonneg_right (mul_nonneg (Nat.cast_nonneg _) hh.le)
  have hU : 0 < U := (lt_trans zero_lt_one hx).trans_le hxU
  have hlog : Real.log x ≤ Real.log U := Real.log_le_log (lt_trans zero_lt_one hx) hxU
  have hlogU : 0 ≤ Real.log U := Real.log_nonneg (hx.le.trans hxU)
  have hp : U ^ (s.re + (m + 3 : ℕ)) ≤ U ^ (m + 4) * Real.exp (-δ * Real.log x) := by
    calc
      _ = Real.exp (Real.log U * (s.re + (m + 3 : ℕ))) := Real.rpow_def_of_pos hU _
      _ ≤ Real.exp (Real.log U * (m + 4 : ℕ) + (-δ * Real.log x)) := by
        apply Real.exp_le_exp.mpr
        have hb := mul_le_mul_of_nonneg_left hβ hlogU
        have hd := mul_le_mul_of_nonneg_left hlog hδ
        push_cast at *
        nlinarith only [hb, hd]
      _ = _ := by rw [Real.exp_add, ← Real.rpow_def_of_pos hU, Real.rpow_natCast]
  refine he.trans ?_
  have hb := div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_left hp (by positivity : (0 : ℝ) ≤ 2 ^ (m + 3)))
    (by positivity : 0 ≤ h ^ (m + 3) * |s.im| ^ (m + 4))
  change 2 ^ (m + 3) * U ^ (s.re + (m + 3 : ℕ)) /
    (h ^ (m + 3) * |s.im| ^ (m + 4)) ≤ _
  exact hb.trans_eq (by dsimp [U]; ring)

/-- Beyond a positive cutoff, keep the damping factor in the inverse-square kernel. -/
theorem norm_dusartBox_paired_atom_le_tail_kernel_gap (m : ℕ) {h x T δ : ℝ}
    (hh : 0 < h) (hx : 1 < x) (hT : 0 < T) (hδ : 0 ≤ δ) {s : ℂ}
    (hβ0 : 0 ≤ s.re) (hβ : s.re ≤ 1 - δ) (hγ : T ≤ |s.im|) :
    ‖finiteLaplace (fun u => (dusartBoxWeight m h x u : ℂ)) (dusartBoxSupport m h x) (-s) +
        1 / s‖ ≤
      dusartBoxTailFactor m h x T * (Real.exp (-δ * Real.log x) / s.im ^ 2) := by
  have hγpos := hT.trans_le hγ
  have hs := abs_pos.mp hγpos
  refine (norm_dusartBox_paired_atom_le_height_gap m hh hx hδ hs hβ0 hβ).trans ?_
  have hp : T ^ (m + 2) ≤ |s.im| ^ (m + 2) := pow_le_pow_left₀ hT.le hγ _
  have hd : h ^ (m + 3) * (T ^ (m + 2) * s.im ^ 2) ≤
      h ^ (m + 3) * |s.im| ^ (m + 4) := by
    rw [show m + 4 = (m + 2) + 2 by omega, pow_add |s.im| (m + 2) 2, sq_abs]
    exact mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_right hp (sq_nonneg _)) (by positivity)
  have he := div_le_div_of_nonneg_left
    (by positivity : 0 ≤ 2 ^ (m + 3) * (x + (m + 3 : ℕ) * h) ^ (m + 4))
    (show 0 < h ^ (m + 3) * (T ^ (m + 2) * s.im ^ 2) by positivity) hd
  exact (mul_le_mul_of_nonneg_right he (Real.exp_pos _).le).trans_eq
    (by unfold dusartBoxTailFactor; ring)

/-- The proved region supplies height-dependent damping for every actual high xi zero. -/
theorem norm_dusartBox_xi_atom_le_initial_tail_kernel (m : ℕ) {h x T : ℝ}
    (hh : 0 < h) (hx : 1 < x) (hT : 10 ^ 9 ≤ T)
    (p : RiemannXiDivisorZeroIndex) (hp : T ≤ |(riemannXiDivisorZeroValue p).im|) :
    ‖iteratedBoxAverageComplex h (m + 3)
        (fun t => (t : ℂ) ^ riemannXiDivisorZeroValue p / riemannXiDivisorZeroValue p) x‖ ≤
      dusartBoxTailFactor m h x T *
        (Real.exp (-(1 / (56 * Real.log |(riemannXiDivisorZeroValue p).im|)) * Real.log x) /
          (riemannXiDivisorZeroValue p).im ^ 2) := by
  rw [← finiteLaplace_dusartBoxWeight_add_inv m hh hx (riemannXiDivisorZeroValue_ne_zero p)]
  have ht := hT.trans hp
  have hl : 0 < Real.log |(riemannXiDivisorZeroValue p).im| := Real.log_pos (by linarith)
  exact norm_dusartBox_paired_atom_le_tail_kernel_gap m hh hx (by linarith) (by positivity)
    (riemannXi_zero_mem_critical_strip (riemannXiDivisorZeroValue_eq_zero p)).1
    (by linarith [xi_zero_gap_initial (riemannXiDivisorZeroValue_eq_zero p) ht]) hp

end

end PrimeFactorUnimodality
