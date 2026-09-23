import PrimeFactorUnimodality.Helpers.Analytic.DusartBoxPowerTransform
import PrimeFactorUnimodality.Mathlib.MeasureTheory.Integral.IntervalIntegral.IteratedAveragePower

/-! # Explicit height decay of the actual Dusart box atom

The averaged power is the forward difference of its higher primitive.
Bounding that difference gains one height denominator per averaging step.
For exponents in the critical strip, a positive cutoff leaves an explicit
multiple of the inverse-square height kernel used by the proved xi tails.
-/

namespace PrimeFactorUnimodality

noncomputable section

open Complex Function intervalIntegral

theorem finiteLaplace_dusartBoxWeight_eq_difference (m : ℕ) {h x : ℝ}
    (hh : 0 < h) (hx : 1 < x) {s : ℂ} (hs : s.im ≠ 0) :
    finiteLaplace (fun u => (dusartBoxWeight m h x u : ℂ)) (dusartBoxSupport m h x) (-s) +
        1 / s = ((fwdDiff h)^[m + 3] (fun t : ℝ => (t : ℂ) ^ (s + (m + 3 : ℕ)))) x /
          ((h : ℂ) ^ (m + 3) * cpowPrimitiveDenom s (m + 3)) := by
  have hs0 : s ≠ 0 := fun he => hs (by simp [he])
  rw [finiteLaplace_dusartBoxWeight_add_inv m hh hx hs0]
  exact iteratedBoxAverageComplex_cpow_div_eq_difference hh (lt_trans zero_lt_one hx)
    (add_natCast_ne_zero_of_im_ne_zero hs) (m + 3)

theorem norm_dusartBox_paired_atom_le_height (m : ℕ) {h x : ℝ}
    (hh : 0 < h) (hx : 1 < x) {s : ℂ} (hs : s.im ≠ 0)
    (hβ0 : 0 ≤ s.re) (hβ1 : s.re ≤ 1) :
    ‖finiteLaplace (fun u => (dusartBoxWeight m h x u : ℂ)) (dusartBoxSupport m h x) (-s) +
        1 / s‖ ≤
      2 ^ (m + 3) * (x + (m + 3 : ℕ) * h) ^ (m + 4) /
        (h ^ (m + 3) * |s.im| ^ (m + 4)) := by
  have hs0 : s ≠ 0 := fun he => hs (by simp [he])
  rw [finiteLaplace_dusartBoxWeight_add_inv m hh hx hs0]
  have he := norm_iteratedBoxAverageComplex_cpow_div_le_height hh
    (lt_trans zero_lt_one hx) hs hβ0 (m + 3)
  refine he.trans (div_le_div_of_nonneg_right ?_ (by positivity))
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  have hU : 1 ≤ x + (m + 3 : ℕ) * h :=
    hx.le.trans (le_add_of_nonneg_right (mul_nonneg (Nat.cast_nonneg _) hh.le))
  have hp := Real.rpow_le_rpow_of_exponent_le hU
    (show s.re + (m + 3 : ℕ) ≤ (m + 4 : ℕ) by push_cast; linarith)
  simpa only [Real.rpow_natCast] using hp

/-- The coefficient of the inverse-square kernel after the high cutoff. -/
def dusartBoxTailFactor (m : ℕ) (h x T : ℝ) : ℝ :=
  2 ^ (m + 3) * (x + (m + 3 : ℕ) * h) ^ (m + 4) /
    (h ^ (m + 3) * T ^ (m + 2))

theorem norm_dusartBox_paired_atom_le_tail_kernel (m : ℕ) {h x T : ℝ}
    (hh : 0 < h) (hx : 1 < x) (hT : 0 < T) {s : ℂ}
    (hβ0 : 0 ≤ s.re) (hβ1 : s.re ≤ 1) (hγ : T ≤ |s.im|) :
    ‖finiteLaplace (fun u => (dusartBoxWeight m h x u : ℂ)) (dusartBoxSupport m h x) (-s) +
        1 / s‖ ≤ dusartBoxTailFactor m h x T * (1 / s.im ^ 2) := by
  have hγpos := hT.trans_le hγ
  have hs := abs_pos.mp hγpos
  refine (norm_dusartBox_paired_atom_le_height m hh hx hs hβ0 hβ1).trans ?_
  have hp : T ^ (m + 2) ≤ |s.im| ^ (m + 2) := pow_le_pow_left₀ hT.le hγ _
  have hd : h ^ (m + 3) * (T ^ (m + 2) * s.im ^ 2) ≤
      h ^ (m + 3) * |s.im| ^ (m + 4) := by
    rw [show m + 4 = (m + 2) + 2 by omega, pow_add |s.im| (m + 2) 2, sq_abs]
    exact mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_right hp (sq_nonneg _)) (by positivity)
  have hnum : 0 ≤ 2 ^ (m + 3) * (x + (m + 3 : ℕ) * h) ^ (m + 4) := by positivity
  have he := div_le_div_of_nonneg_left hnum
    (show 0 < h ^ (m + 3) * (T ^ (m + 2) * s.im ^ 2) by positivity) hd
  refine he.trans_eq ?_
  unfold dusartBoxTailFactor
  ring

end

end PrimeFactorUnimodality
