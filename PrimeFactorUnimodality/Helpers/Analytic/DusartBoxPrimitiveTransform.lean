import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import PrimeFactorUnimodality.Helpers.Analytic.DusartBoxDistributionIntegral

/-! # Primitive evaluation of the logarithmic box transform

The substitution `t=exp(u)` converts the actual finite logarithmic cutoff
integral to the distribution integral. Fubini then identifies it with an
iterated average of a primitive. The hypotheses are local to the positive
arithmetic interval, permitting logarithmic and complex-power components.
-/

namespace PrimeFactorUnimodality

noncomputable section

open Real Set intervalIntegral

/-- A logarithmic box integral is the exact average of the arithmetic primitive. -/
theorem integral_dusartBoxWeight_mul_comp_exp (m : ℕ) {h x : ℝ}
    (hh : 0 < h) (hx : 1 < x) {g : ℝ → ℝ}
    (hg : ContinuousOn g (Icc 1 (x + (m + 3 : ℕ) * h))) :
    (∫ u in (0 : ℝ)..dusartBoxSupport m h x,
      dusartBoxWeight m h x u * (g (exp u) * exp u)) =
      iteratedBoxAverage h (m + 3) (fun v => ∫ t in (1 : ℝ)..v, g t) x := by
  have hd := dusartBoxSupport_pos m hh hx
  have hU : 0 < x + (m + 3 : ℕ) * h :=
    add_pos_of_pos_of_nonneg (lt_trans zero_lt_one hx)
      (mul_nonneg (Nat.cast_nonneg _) hh.le)
  have hD : Continuous (fun t => dusartBoxDistribution m h (x - t)) :=
    (contDiff_dusartBoxDistribution m hh).continuous.comp (continuous_const.sub continuous_id)
  have hG := hD.continuousOn.mul hg
  have he := integral_comp_mul_deriv'
    (a := 0) (b := dusartBoxSupport m h x) (f := exp) (f' := exp)
    (g := fun t => dusartBoxDistribution m h (x - t) * g t)
    (fun u _ => hasDerivAt_exp u) continuous_exp.continuousOn
    (hG.mono (by
      rintro t ⟨u, hu, rfl⟩
      rw [uIcc_of_le hd.le] at hu
      refine ⟨one_le_exp_iff.mpr hu.1, ?_⟩
      have hu' := exp_le_exp.mpr hu.2
      simpa only [dusartBoxSupport, exp_log hU] using hu'))
  simp only [Function.comp_apply, exp_zero, dusartBoxSupport, exp_log hU] at he
  calc
    _ = ∫ t in (1 : ℝ)..x + (m + 3 : ℕ) * h,
        dusartBoxDistribution m h (x - t) * g t := by
      simpa only [dusartBoxWeight, dusartBoxSupport, mul_assoc] using he
    _ = _ := integral_dusartStepAverage_mul (m + 3) hh hg hx.le le_rfl

/-- A proved primitive on the arithmetic interval evaluates the logarithmic box integral. -/
theorem integral_dusartBoxWeight_mul_deriv_exp (m : ℕ) {h x : ℝ}
    (hh : 0 < h) (hx : 1 < x) {f g : ℝ → ℝ}
    (hg : ContinuousOn g (Icc 1 (x + (m + 3 : ℕ) * h)))
    (hfg : ∀ t ∈ Icc 1 (x + (m + 3 : ℕ) * h), HasDerivAt f (g t) t) :
    (∫ u in (0 : ℝ)..dusartBoxSupport m h x,
      dusartBoxWeight m h x u * (g (exp u) * exp u)) =
      iteratedBoxAverage h (m + 3) (fun v => f v - f 1) x := by
  rw [integral_dusartBoxWeight_mul_comp_exp m hh hx hg]
  apply iteratedBoxAverage_congr_on hh.le
  intro v hv
  have hv1 : 1 ≤ v := hx.le.trans hv.1
  have hsub : uIcc 1 v ⊆ Icc 1 (x + (m + 3 : ℕ) * h) := by
    rw [uIcc_of_le hv1]
    exact Icc_subset_Icc le_rfl hv.2
  exact integral_eq_sub_of_hasDerivAt (fun t ht => hfg t (hsub ht))
    (hg.mono hsub).intervalIntegrable

end

end PrimeFactorUnimodality
