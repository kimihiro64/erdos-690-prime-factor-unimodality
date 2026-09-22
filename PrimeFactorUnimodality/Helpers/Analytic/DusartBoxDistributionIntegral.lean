import Mathlib.MeasureTheory.Integral.Prod
import PrimeFactorUnimodality.Helpers.Analytic.DusartBoxCutoff

/-! # Integrating the averaged step against a continuous test function

On a fixed interval containing the complete box support, integrating the
averaged step is exactly averaging the primitive. Bounded monotone step
averages justify Fubini even at order zero, where the step has a jump.
This supplies the arithmetic-variable transform of the actual cutoff.
-/

namespace PrimeFactorUnimodality

noncomputable section

open MeasureTheory Set intervalIntegral

theorem dusartStepAverage_mem_Icc (n : ℕ) {h : ℝ} (hh : 0 < h) (t : ℝ) :
    iteratedBoxAverage h n dusartUnitStep t ∈ Icc (0 : ℝ) 1 := by
  have he := iteratedBoxAverage_mem_Icc hh monotone_dusartUnitStep n t
  exact ⟨(dusartUnitStep_mem_Icc t).1.trans he.1,
    he.2.trans (dusartUnitStep_mem_Icc _).2⟩

private theorem integrable_stepAverage_rectangle (n : ℕ) {h a b : ℝ} (hh : 0 < h)
    {g : ℝ → ℝ} (hg : ContinuousOn g (Icc a b)) (x : ℝ) :
    Integrable (fun p : ℝ × ℝ => iteratedBoxAverage h n dusartUnitStep (x + p.1 - p.2) *
      g p.2) ((volume.restrict (Icc 0 h)).prod (volume.restrict (Icc a b))) := by
  rw [Measure.prod_restrict]
  have hgc : ContinuousOn (fun p : ℝ × ℝ => g p.2) (Icc 0 h ×ˢ Icc a b) :=
    hg.comp continuous_snd.continuousOn (fun _ hp => hp.2)
  have hgi := hgc.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)
    (μ := volume.prod volume)
  have hm : Measurable (fun p : ℝ × ℝ =>
      iteratedBoxAverage h n dusartUnitStep (x + p.1 - p.2)) :=
    (monotone_iteratedBoxAverage hh monotone_dusartUnitStep n).measurable.comp
      ((measurable_const.add measurable_fst).sub measurable_snd)
  apply Integrable.mono hgi (hm.aestronglyMeasurable.mul hgi.aestronglyMeasurable)
  apply Filter.Eventually.of_forall
  intro p
  have hb := dusartStepAverage_mem_Icc n hh (x + p.1 - p.2)
  dsimp only [Pi.mul_apply]
  rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg hb.1]
  exact mul_le_of_le_one_left (norm_nonneg _) hb.2

/-- The genuine weighted-step integrand is integrable on the complete rectangle. -/
theorem integral_dusartStepAverage_swap (n : ℕ) {h a b : ℝ} (hh : 0 < h) (hab : a ≤ b)
    {g : ℝ → ℝ} (hg : ContinuousOn g (Icc a b)) (x : ℝ) :
    (∫ u in (0 : ℝ)..h, ∫ t in a..b,
      iteratedBoxAverage h n dusartUnitStep (x + u - t) * g t) =
      ∫ t in a..b, ∫ u in (0 : ℝ)..h,
        iteratedBoxAverage h n dusartUnitStep (x + u - t) * g t := by
  have he := MeasureTheory.integral_integral_swap
    (f := fun u t => iteratedBoxAverage h n dusartUnitStep (x + u - t) * g t)
    (integrable_stepAverage_rectangle n hh hg x)
  simp_rw [integral_Icc_eq_integral_Ioc] at he
  simpa only [integral_of_le hh.le, integral_of_le hab] using he

/-- Integrating a translated unit step truncates exactly at its arithmetic cutoff. -/
theorem integral_dusartUnitStep_mul (g : ℝ → ℝ) {a b x : ℝ} (hax : a ≤ x) (hxb : x ≤ b) :
    (∫ t in a..b, dusartUnitStep (x - t) * g t) = ∫ t in a..x, g t := by
  have he : (fun t => dusartUnitStep (x - t) * g t) = (Iic x).indicator g := by
    funext t
    simp only [dusartUnitStep, indicator, mem_Iic, sub_nonneg]
    split_ifs <;> simp
  have hs : Icc a b ∩ Iic x = Icc a x := by
    ext t
    simp only [mem_inter_iff, mem_Icc, mem_Iic]
    exact ⟨fun ht => ⟨ht.1.1, ht.2⟩, fun ht => ⟨⟨ht.1, ht.2.trans hxb⟩, ht.2⟩⟩
  rw [he, integral_of_le (hax.trans hxb), ← integral_Icc_eq_integral_Ioc,
    setIntegral_indicator measurableSet_Iic, hs, integral_Icc_eq_integral_Ioc,
    ← integral_of_le hax]

/-- The weighted distribution integral is the actual iterated average of the primitive. -/
theorem integral_dusartStepAverage_mul (n : ℕ) {h a b x : ℝ} (hh : 0 < h)
    {g : ℝ → ℝ} (hg : ContinuousOn g (Icc a b))
    (hax : a ≤ x) (hxb : x + n * h ≤ b) :
    (∫ t in a..b, iteratedBoxAverage h n dusartUnitStep (x - t) * g t) =
      iteratedBoxAverage h n (fun v => ∫ t in a..v, g t) x := by
  induction n generalizing x with
  | zero =>
    exact integral_dusartUnitStep_mul g hax (by simpa using hxb)
  | succ n ih =>
    have hab : a ≤ b := by
      have hm : 0 ≤ (n + 1 : ℕ) * h := mul_nonneg (Nat.cast_nonneg _) hh.le
      linarith
    have he (t : ℝ) : iteratedBoxAverage h (n + 1) dusartUnitStep (x - t) * g t =
        h⁻¹ * ∫ u in (0 : ℝ)..h,
          iteratedBoxAverage h n dusartUnitStep (x + u - t) * g t := by
      change (h⁻¹ * ∫ u in (0 : ℝ)..h,
        iteratedBoxAverage h n dusartUnitStep (x - t + u)) * g t = _
      rw [intervalIntegral.integral_mul_const]
      have hi : (∫ u in (0 : ℝ)..h,
          iteratedBoxAverage h n dusartUnitStep (x - t + u)) =
          ∫ u in (0 : ℝ)..h, iteratedBoxAverage h n dusartUnitStep (x + u - t) := by
        apply integral_congr
        intro u _
        dsimp only
        exact congrArg (iteratedBoxAverage h n dusartUnitStep) (by ring)
      rw [hi]
      ring
    simp_rw [he]
    rw [intervalIntegral.integral_const_mul, ← integral_dusartStepAverage_swap n hh hab hg x]
    change h⁻¹ * (∫ u in (0 : ℝ)..h,
      ∫ t in a..b, iteratedBoxAverage h n dusartUnitStep (x + u - t) * g t) =
      h⁻¹ * ∫ u in (0 : ℝ)..h,
        iteratedBoxAverage h n (fun v => ∫ t in a..v, g t) (x + u)
    congr 1
    apply integral_congr
    intro u hu
    rw [uIcc_of_le hh.le] at hu
    apply ih
    · linarith [hu.1]
    · push_cast at hxb
      linarith [hu.2]

end

end PrimeFactorUnimodality
