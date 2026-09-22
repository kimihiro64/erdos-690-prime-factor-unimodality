import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import PrimeFactorUnimodality.Mathlib.MeasureTheory.Integral.IntervalIntegral.IteratedAverageRegularity
import PrimeFactorUnimodality.Mathlib.MeasureTheory.Integral.IntervalIntegral.IteratedAverageSupport

/-! # The additive box cutoff for Dusart's averaged explicit formula

Average the unit step at least three times, then translate its cutoff by
`exp(u)`. The resulting logarithmic weight has two continuous derivatives,
values in `[0,1]`, a plateau at one, and an exact finite support endpoint.
These are analytic identities for every positive width, not finite data.
-/

namespace PrimeFactorUnimodality

noncomputable section

open Real Set intervalIntegral

/-- The step whose translates select the terms of a Chebyshev sum. -/
def dusartUnitStep (t : ℝ) : ℝ := if 0 ≤ t then 1 else 0

theorem monotone_dusartUnitStep : Monotone dusartUnitStep := by
  intro x y hxy
  unfold dusartUnitStep
  split_ifs <;> norm_num at *
  linarith

theorem dusartUnitStep_mem_Icc (t : ℝ) : dusartUnitStep t ∈ Icc (0 : ℝ) 1 := by
  unfold dusartUnitStep
  split_ifs <;> norm_num

/-- Three or more averages give the distribution function used in the cutoff. -/
def dusartBoxDistribution (m : ℕ) (h t : ℝ) : ℝ :=
  iteratedBoxAverage h (m + 3) dusartUnitStep t

/-- The distribution is twice continuously differentiable on the entire real line. -/
theorem contDiff_dusartBoxDistribution (m : ℕ) {h : ℝ} (hh : 0 < h) :
    ContDiff ℝ 2 (dusartBoxDistribution m h) := by
  have hc := contDiff_iteratedBoxAverage_succ hh monotone_dusartUnitStep (m + 2)
  exact hc.of_le (by norm_cast; omega)

/-- Averaging preserves the range of the unit step. -/
theorem dusartBoxDistribution_mem_Icc (m : ℕ) {h : ℝ} (hh : 0 < h) (t : ℝ) :
    dusartBoxDistribution m h t ∈ Icc (0 : ℝ) 1 := by
  have he := iteratedBoxAverage_mem_Icc hh monotone_dusartUnitStep (m + 3) t
  exact ⟨(dusartUnitStep_mem_Icc t).1.trans he.1,
    he.2.trans (dusartUnitStep_mem_Icc _).2⟩

/-- The entire averaging support is in the upper plateau when its left endpoint is nonnegative. -/
theorem dusartBoxDistribution_eq_one (m : ℕ) {h t : ℝ} (hh : 0 < h) (ht : 0 ≤ t) :
    dusartBoxDistribution m h t = 1 := by
  apply iteratedBoxAverage_eq_const hh
  intro u hu
  simp [dusartUnitStep, ht.trans hu.1]

/-- The lower plateau includes the exact boundary by continuity of the averaged step. -/
theorem dusartBoxDistribution_eq_zero (m : ℕ) {h t : ℝ} (hh : 0 < h)
    (ht : t + (m + 3 : ℕ) * h ≤ 0) : dusartBoxDistribution m h t = 0 := by
  have he : EqOn (dusartBoxDistribution m h) (fun _ => 0) (Iio (-(m + 3 : ℕ) * h)) := by
    intro v hv
    apply iteratedBoxAverage_eq_const hh
    intro u hu
    have hu' : u < 0 := by
      change v < -(m + 3 : ℕ) * h at hv
      linarith [hu.2]
    simp [dusartUnitStep, not_le.mpr hu']
  apply he.closure (contDiff_dusartBoxDistribution m hh).continuous continuous_const
  rw [closure_Iio]
  change t ≤ -(m + 3 : ℕ) * h
  linarith

/-- The finite-support weight on the logarithmic variable in the explicit formula. -/
def dusartBoxWeight (m : ℕ) (h x u : ℝ) : ℝ :=
  dusartBoxDistribution m h (x - exp u)

/-- The logarithm of the maximal arithmetic endpoint. -/
def dusartBoxSupport (m : ℕ) (h x : ℝ) : ℝ := log (x + (m + 3 : ℕ) * h)

theorem contDiff_dusartBoxWeight (m : ℕ) {h : ℝ} (hh : 0 < h) (x : ℝ) :
    ContDiff ℝ 2 (dusartBoxWeight m h x) :=
  (contDiff_dusartBoxDistribution m hh).comp (contDiff_const.sub Real.contDiff_exp)

theorem dusartBoxWeight_mem_Icc (m : ℕ) {h : ℝ} (hh : 0 < h) (x u : ℝ) :
    dusartBoxWeight m h x u ∈ Icc (0 : ℝ) 1 := dusartBoxDistribution_mem_Icc m hh _

theorem dusartBoxWeight_zero (m : ℕ) {h x : ℝ} (hh : 0 < h) (hx : 1 ≤ x) :
    dusartBoxWeight m h x 0 = 1 := by
  apply dusartBoxDistribution_eq_one m hh
  simpa using sub_nonneg.mpr hx

theorem dusartBoxSupport_pos (m : ℕ) {h x : ℝ} (hh : 0 < h) (hx : 1 < x) :
    0 < dusartBoxSupport m h x := by
  apply log_pos
  have hm : 0 ≤ (m + 3 : ℕ) * h := mul_nonneg (Nat.cast_nonneg _) hh.le
  linarith

/-- The weight vanishes at and beyond its exact support endpoint. -/
theorem dusartBoxWeight_eq_zero (m : ℕ) {h x u : ℝ} (hh : 0 < h) (hx : 0 < x)
    (hu : dusartBoxSupport m h x ≤ u) : dusartBoxWeight m h x u = 0 := by
  apply dusartBoxDistribution_eq_zero m hh
  have hx' : 0 < x + (m + 3 : ℕ) * h :=
    add_pos_of_pos_of_nonneg hx (mul_nonneg (Nat.cast_nonneg _) hh.le)
  have he : x + (m + 3 : ℕ) * h ≤ exp u := (log_le_iff_le_exp hx').mp hu
  linarith

end

end PrimeFactorUnimodality
