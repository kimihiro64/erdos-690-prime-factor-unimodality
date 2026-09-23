import PrimeFactorUnimodality.Helpers.Analytic.DusartBoxHeightGap
import PrimeFactorUnimodality.Helpers.Analytic.DusartBoxHighTail

/-! # The complete high-zero tail with initial-region damping retained

The positive damping factor is at most one, so the already proved
inverse-square summability controls this weighted series. The actual
box tail inherits the stronger estimate without any additional zero
location premise. Quantitative integration of the damped kernel remains
separate from this exact, multiplicity-preserving summation step.
-/

namespace PrimeFactorUnimodality

noncomputable section

open intervalIntegral

/-- The height kernel retaining the actual initial-region exponential factor. -/
def xiInitialDampedHeightKernel (x : ℝ) (p : RiemannXiDivisorZeroIndex) : ℝ :=
  Real.exp (-(1 / (56 * Real.log |(riemannXiDivisorZeroValue p).im|)) * Real.log x) /
    (riemannXiDivisorZeroValue p).im ^ 2

theorem xiInitialDampedHeightKernel_nonneg (x : ℝ) (p : RiemannXiDivisorZeroIndex) :
    0 ≤ xiInitialDampedHeightKernel x p := by unfold xiInitialDampedHeightKernel; positivity

theorem xiInitialDampedHeightKernel_le_inv_sq {x T : ℝ} (hx : 1 ≤ x) (hT : 10 ^ 9 ≤ T)
    (p : RiemannXiDivisorZeroIndex) (hp : T ≤ |(riemannXiDivisorZeroValue p).im|) :
    xiInitialDampedHeightKernel x p ≤ 1 / (riemannXiDivisorZeroValue p).im ^ 2 := by
  have hl : 0 < Real.log |(riemannXiDivisorZeroValue p).im| := Real.log_pos (by linarith)
  have he : Real.exp (-(1 / (56 * Real.log |(riemannXiDivisorZeroValue p).im|)) *
      Real.log x) ≤ 1 := Real.exp_le_one_iff.mpr
    (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (by positivity)) (Real.log_nonneg hx))
  exact div_le_div_of_nonneg_right he (sq_nonneg _)

theorem summable_xiInitialDampedHeightKernel {x T : ℝ} (hx : 1 ≤ x) (hT : 10 ^ 9 ≤ T) :
    Summable (fun p : {p : RiemannXiDivisorZeroIndex //
      T ≤ |(riemannXiDivisorZeroValue p).im|} => xiInitialDampedHeightKernel x p.1) := by
  have hs := summable_xiHeightTail (by linarith : 0 < T) 0
  have hpred : (fun p : RiemannXiDivisorZeroIndex => |(0 : ℝ)| + T ≤
      |(riemannXiDivisorZeroValue p).im|) =
      (fun p => T ≤ |(riemannXiDivisorZeroValue p).im|) := by funext p; simp
  rw [hpred] at hs
  simp only [zero_sub, neg_sq] at hs
  exact Summable.of_nonneg_of_le (fun p => xiInitialDampedHeightKernel_nonneg x p.1)
    (fun p => xiInitialDampedHeightKernel_le_inv_sq hx hT p.1 p.2) hs

/-- The full closed high-height series, with both signs and every multiplicity retained. -/
def xiInitialDampedHeightTail (x T : ℝ) : ℝ :=
  ∑' p : {p : RiemannXiDivisorZeroIndex // T ≤ |(riemannXiDivisorZeroValue p).im|},
    xiInitialDampedHeightKernel x p.1

theorem xiInitialDampedHeightTail_le_heightTail {x T : ℝ} (hx : 1 ≤ x) (hT : 10 ^ 9 ≤ T) :
    xiInitialDampedHeightTail x T ≤ xiHeightTail 0 T := by
  have hs := summable_xiHeightTail (by linarith : 0 < T) 0
  have hpred : (fun p : RiemannXiDivisorZeroIndex => |(0 : ℝ)| + T ≤
      |(riemannXiDivisorZeroValue p).im|) =
      (fun p => T ≤ |(riemannXiDivisorZeroValue p).im|) := by funext p; simp
  rw [hpred] at hs
  simp only [zero_sub, neg_sq] at hs
  rw [xiInitialDampedHeightTail, xiHeightTail_zero_eq_tsum]
  exact (summable_xiInitialDampedHeightKernel hx hT).tsum_le_tsum
    (fun p => xiInitialDampedHeightKernel_le_inv_sq hx hT p.1 p.2) hs

/-- The actual box high sum satisfies the damped bound, with no supplied zero-free input. -/
theorem norm_dusartBoxXiHighSum_le_initialDampedTail (m : ℕ) {h x T : ℝ}
    (hh : 0 < h) (hx : 1 < x) (hT : 10 ^ 9 ≤ T) :
    ‖dusartBoxXiHighSum m h x T‖ ≤
      dusartBoxTailFactor m h x T * xiInitialDampedHeightTail x T := by
  let P : RiemannXiDivisorZeroIndex → Prop := fun p => T ≤ |(riemannXiDivisorZeroValue p).im|
  have ha := ((summable_dusartBox_xi_power_average m hh hx).subtype P).norm
  have hb := (summable_xiInitialDampedHeightKernel hx.le hT).mul_left
    (dusartBoxTailFactor m h x T)
  calc
    ‖dusartBoxXiHighSum m h x T‖ ≤ _ := norm_tsum_le_tsum_norm ha
    _ ≤ ∑' p : {p : RiemannXiDivisorZeroIndex // P p},
        dusartBoxTailFactor m h x T * xiInitialDampedHeightKernel x p.1 :=
      ha.tsum_le_tsum (fun p => norm_dusartBox_xi_atom_le_initial_tail_kernel m hh hx hT p.1 p.2) hb
    _ = _ := by rw [tsum_mul_left]; rfl

end

end PrimeFactorUnimodality
