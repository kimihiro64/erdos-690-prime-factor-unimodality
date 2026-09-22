import Mathlib.Analysis.SpecificLimits.Basic
import PrimeFactorUnimodality.Helpers.Analytic.BacklundRealZeros
import PrimeFactorUnimodality.Mathlib.Analysis.Complex.Log.Interval
import PrimeFactorUnimodality.Mathlib.Analysis.SpecialFunctions.Trigonometric.ZeroCount

/-! # Horizontal argument change from Backlund's real-part crossings

For a continuous logarithm of the actual surrogate on a nonvanishing
horizontal segment, each power's real-part zeros bound the change of its
imaginary part. Taking the unbounded good powers in Jensen's estimate
removes both the endpoint crossing allowance and the fixed centre loss.
The resulting bound retains only the circle-to-centre logarithmic ratio.
The final theorem constructs the logarithm using the exponential covering.

This proves the horizontal argument estimate under explicit boundary norm
and nonvanishing hypotheses; it is not the numerical zero-count theorem.
-/

namespace PrimeFactorUnimodality

noncomputable section

open Complex Filter Metric Real Set
open scoped Topology

/-- The real-part zeros of any positive power bound the logarithm's imaginary increment. -/
theorem backlund_log_im_sub_le_zeroCount {T σ r a b : ℝ} {n : ℕ} {L : ℝ → ℂ}
    (hab : a ≤ b) (hr : 0 ≤ r) (hn : 0 < n)
    (hseg : ∀ x ∈ Icc a b, |x - σ| ≤ r)
    (hL : ContinuousOn L (Icc a b))
    (hlog : ∀ x ∈ Icc a b, Complex.exp (L x) = Backlund.zetaSurrogate ((x : ℂ) + T * I))
    (hc : backlundAuxiliary T n σ ≠ 0) :
    |(L b).im - (L a).im| ≤ (backlundRealZeroCount T n σ r + 1 : ℝ) * Real.pi / n := by
  classical
  have hf := finite_backlundRealZeros hr hc
  have hphase : ContinuousOn (fun x => (n : ℝ) * (L x).im) (Icc a b) :=
    continuousOn_const.mul (Complex.continuous_im.comp_continuousOn hL)
  have hbound := hphase.abs_sub_le_card_add_one_mul_pi_of_cos_eq_zero hab hf.toFinset (by
    intro x hx hcos
    apply hf.mem_toFinset.mpr
    refine ⟨hseg x hx, ?_⟩
    rw [← hlog x hx, ← Complex.exp_nat_mul, Complex.exp_re]
    simpa using congrArg (fun y : ℝ => Real.exp ((n : ℝ) * (L x).re) * y) hcos)
  have hcard : hf.toFinset.card = backlundRealZeroCount T n σ r :=
    (Set.ncard_eq_toFinset_card _ hf).symm
  rw [hcard, ← mul_sub, abs_mul, abs_of_nonneg (Nat.cast_nonneg n)] at hbound
  apply (le_div_iff₀ (show (0 : ℝ) < n by exact_mod_cast hn)).mpr
  simpa only [mul_comm] using hbound

/-- The infinite-power limit removes all fixed losses from the horizontal Jensen estimate. -/
theorem backlund_log_im_sub_le_jensen {T σ r R M a b : ℝ} {L : ℝ → ℂ}
    (hσ : 1 < σ) (hr : 0 < r) (hrR : r < R) (hM : 1 ≤ M)
    (hab : a ≤ b) (hseg : ∀ x ∈ Icc a b, |x - σ| ≤ r)
    (hL : ContinuousOn L (Icc a b))
    (hlog : ∀ x ∈ Icc a b, Complex.exp (L x) = Backlund.zetaSurrogate ((x : ℂ) + T * I))
    (hp : ∀ z ∈ sphere (σ : ℂ) R, ‖Backlund.zetaSurrogate (z + T * I)‖ ≤ M)
    (hm : ∀ z ∈ sphere (σ : ℂ) R, ‖Backlund.zetaSurrogate (z - T * I)‖ ≤ M) :
    |(L b).im - (L a).im| ≤ Real.pi *
      (Real.log (M / ‖Backlund.zetaSurrogate ((σ : ℂ) + T * I)‖) / Real.log (R / r)) := by
  let B := Real.log (M / ‖Backlund.zetaSurrogate ((σ : ℂ) + T * I)‖) / Real.log (R / r)
  let C := Real.log 2 / Real.log (R / r) + 1
  have hfreq : ∃ᶠ n : ℕ in atTop,
      |(L b).im - (L a).im| ≤ Real.pi * (B + C / n) := by
    apply ((frequently_backlundAuxiliary_centre_lower hσ T).and_eventually
      (eventually_gt_atTop 0)).mono
    rintro n ⟨hc, hn⟩
    have hnR : (0 : ℝ) < n := by exact_mod_cast hn
    have hA : 0 < ‖Backlund.zetaSurrogate ((σ : ℂ) + T * I)‖ :=
      norm_pos_iff.mpr (backlund_surrogate_ne_zero_of_one_lt_re (by simpa using hσ))
    have hcne : backlundAuxiliary T n σ ≠ 0 :=
      norm_pos_iff.mp ((div_pos (pow_pos hA n) (by norm_num)).trans_le hc)
    have harg := backlund_log_im_sub_le_zeroCount hab hr.le hn hseg hL hlog hcne
    have hcount := backlundRealZeroCount_le hσ hr hrR hM hc hp hm
    have hcount' : (backlundRealZeroCount T n σ r + 1 : ℝ) ≤ (n : ℝ) * B + C := by
      dsimp [B, C]
      calc
        _ ≤ (((n : ℝ) * Real.log (M / ‖Backlund.zetaSurrogate ((σ : ℂ) + T * I)‖) +
            Real.log 2) / Real.log (R / r)) + 1 := by
          simpa [add_comm] using add_le_add_right hcount 1
        _ = _ := by ring
    calc
      _ ≤ (backlundRealZeroCount T n σ r + 1 : ℝ) * Real.pi / n := harg
      _ ≤ ((n : ℝ) * B + C) * Real.pi / n :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hcount' Real.pi_pos.le) hnR.le
      _ = Real.pi * (B + C / n) := by field_simp
  have hlim : Tendsto (fun n : ℕ => Real.pi * (B + C / n)) atTop (𝓝 (Real.pi * B)) := by
    simpa using (tendsto_const_nhds.add (tendsto_const_div_atTop_nhds_zero_nat C)).const_mul Real.pi
  exact ge_of_tendsto_of_frequently hlim hfreq

/-- Every nonvanishing horizontal segment has a continuous logarithm with the Jensen bound. -/
theorem exists_backlund_log_with_argument_bound {T σ r R M a b : ℝ}
    (hσ : 1 < σ) (hr : 0 < r) (hrR : r < R) (hM : 1 ≤ M)
    (hab : a ≤ b) (hseg : ∀ x ∈ Icc a b, |x - σ| ≤ r)
    (hne : ∀ x ∈ Icc a b, Backlund.zetaSurrogate ((x : ℂ) + T * I) ≠ 0)
    (hp : ∀ z ∈ sphere (σ : ℂ) R, ‖Backlund.zetaSurrogate (z + T * I)‖ ≤ M)
    (hm : ∀ z ∈ sphere (σ : ℂ) R, ‖Backlund.zetaSurrogate (z - T * I)‖ ≤ M) :
    ∃ L : ℝ → ℂ, Continuous L ∧
      L a = Complex.log (Backlund.zetaSurrogate ((a : ℂ) + T * I)) ∧
      (∀ x ∈ Icc a b, Complex.exp (L x) = Backlund.zetaSurrogate ((x : ℂ) + T * I)) ∧
      |(L b).im - (L a).im| ≤ Real.pi *
        (Real.log (M / ‖Backlund.zetaSurrogate ((σ : ℂ) + T * I)‖) / Real.log (R / r)) := by
  have hcont : Continuous (fun x : ℝ => Backlund.zetaSurrogate ((x : ℂ) + T * I)) :=
    Backlund.zetaSurrogate_differentiable.continuous.comp (by fun_prop)
  obtain ⟨L, hL, hLa, hlog⟩ := Complex.exists_continuous_log_on_Icc hab hcont.continuousOn hne
    (Complex.exp_log (hne a ⟨le_rfl, hab⟩))
  exact ⟨L, hL, hLa, hlog, backlund_log_im_sub_le_jensen hσ hr hrR hM hab hseg
    hL.continuousOn hlog hp hm⟩

end
end PrimeFactorUnimodality
