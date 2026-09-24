import PrimeFactorUnimodality.Helpers.Analytic.XiAffinePhaseIntervals

/-! # Shared affine coefficients, one-sided errors and domain-boundary checks -/

set_option autoImplicit false

namespace PrimeFactorUnimodality.Tests

open LeanCert.Core XiAffinePhaseIntervals

example {d : XiSimplePhaseIntervals} (hd : d.Valid) {c : SharedTaylorIntervals}
    (hc : c.Prepared) {base : ℚ} (hb : 0 < base) : (prepare d c base).Valid :=
  prepare_valid hd hc hb

example {d : XiAffinePhaseIntervals} (hd : d.Valid) {T : IntervalRat}
    {t : ℝ} (ht : t ∈ T) : xiAffinePhase d.base t ∈ d.affine T := mem_affine hd ht

example {d : XiAffinePhaseIntervals} {p : XiSimplePhaseIntervals} (hp : p.Valid)
    {c : SharedTaylorIntervals} (hc : c.Prepared) (h : d.checkPrepared p c = true) : d.Valid :=
  valid_of_checkPrepared hp hc h

example {d : XiAffinePhaseIntervals} (hd : d.Valid) {T : IntervalRat}
    {t : ℝ} (ht : t ∈ T) (htpos : 0 < t) :
    xiSimplePhase t - xiAffinePhase d.base t ∈ d.remainder T := mem_remainder hd ht htpos

example {d : XiAffinePhaseIntervals} (hd : d.Valid) {T : IntervalRat}
    {t : ℝ} (ht : t ∈ T) (htpos : 0 < t) : xiSimplePhase t ∈ d.evaluate T :=
  mem_evaluate hd ht htpos

example {d : XiAffinePhaseIntervals} (hd : d.Valid) {T : IntervalRat} {t : ℝ}
    (ht : t ∈ T) {phase error : ℚ} (h : d.check T phase error = true) :
    |turingStirlingPhase t - (phase : ℝ)| ≤ (error : ℝ) :=
  abs_stirling_sub_le_of_check hd ht h

example {d : XiAffinePhaseIntervals} (hd : d.Valid) {T : IntervalRat} {t : ℝ}
    (ht : t ∈ T) {phase error : ℚ} (h : d.check T phase error = true) :
    |turingCountingPhase t - (phase : ℝ)| ≤ 1 / 10 + (error : ℝ) :=
  abs_counting_sub_le_of_check hd ht h

def affinePi : IntervalRat := ⟨3, 4, by norm_num⟩
def affineScalar : SharedTaylorIntervals := SharedTaylorIntervals.prepare 0
def affineConstants : XiSimplePhaseIntervals := XiSimplePhaseIntervals.prepare affineScalar affinePi
def preparedAffine : XiAffinePhaseIntervals := prepare affineConstants affineScalar 2
def affineWindow : IntervalRat := ⟨1, 3, by norm_num⟩
def storedAffine : XiAffinePhaseIntervals :=
  ⟨2, ⟨-100, 100, by norm_num⟩, ⟨-100, 100, by norm_num⟩⟩

theorem preparedAffine_valid : preparedAffine.Valid := by
  have hc : affineScalar.Prepared := SharedTaylorIntervals.prepare_prepared 0
  have hd : affineConstants.Valid := XiSimplePhaseIntervals.prepare_valid hc
    (by norm_num [affinePi]) ⟨Real.pi_gt_three.le, Real.pi_lt_four.le⟩
  exact prepare_valid hd hc (by norm_num)

example : storedAffine.checkPrepared affineConstants affineScalar = true := by decide +kernel
example : ({ storedAffine with base := 0 }).checkPrepared affineConstants affineScalar = false :=
  by decide +kernel
example : ({ storedAffine with value := LeanCert.Core.IntervalRat.singleton 100 }).checkPrepared
    affineConstants affineScalar = false := by decide +kernel
example : ({ storedAffine with slope := LeanCert.Core.IntervalRat.singleton 100 }).checkPrepared
    affineConstants affineScalar = false := by decide +kernel

example : storedAffine.Valid := by
  have hc : affineScalar.Prepared := SharedTaylorIntervals.prepare_prepared 0
  have hd : affineConstants.Valid := XiSimplePhaseIntervals.prepare_valid hc
    (by norm_num [affinePi]) ⟨Real.pi_gt_three.le, Real.pi_lt_four.le⟩
  exact valid_of_checkPrepared hd hc (by decide +kernel)

example : (preparedAffine.remainder affineWindow).lo = 0 := by decide +kernel
example : (preparedAffine.remainder affineWindow).hi = 1 / 4 := by decide +kernel
example : preparedAffine.remainder (IntervalRat.singleton 2) = IntervalRat.singleton 0 :=
  by decide +kernel
example : preparedAffine.check affineWindow 0 10 = true := by decide +kernel
example : preparedAffine.check affineWindow 0 0 = false := by decide +kernel
example : preparedAffine.check affineWindow 0 (-1) = false := by decide +kernel
example : preparedAffine.check affineWindow 1000 1 = false := by decide +kernel
example : preparedAffine.check (IntervalRat.singleton 0) 0 1000 = false := by decide +kernel
example : preparedAffine.check (⟨-1, 1, by norm_num⟩ : IntervalRat) 0 1000 = false :=
  by decide +kernel
example : ({ preparedAffine with base := 0 }).check affineWindow 0 1000 = false := by decide +kernel
example : ({ preparedAffine with base := -2 }).check affineWindow 0 1000 = false := by decide +kernel

def exactAffineBudget : ℚ :=
  33 / (16 * affineWindow.lo) + intervalPointRadius (preparedAffine.evaluate affineWindow) 0

example : preparedAffine.check affineWindow 0 exactAffineBudget = true := by decide +kernel
example : preparedAffine.check affineWindow 0 (exactAffineBudget - 1 / 100) = false :=
  by decide +kernel

example {t : ℝ} (ht : t ∈ affineWindow) : |turingStirlingPhase t| ≤ 10 := by
  simpa using abs_stirling_sub_le_of_check preparedAffine_valid ht
    (by decide +kernel : preparedAffine.check affineWindow 0 10 = true)

example {t : ℝ} (ht : t ∈ affineWindow) : |turingCountingPhase t| ≤ 1 / 10 + 10 := by
  simpa using abs_counting_sub_le_of_check preparedAffine_valid ht
    (by decide +kernel : preparedAffine.check affineWindow 0 10 = true)

end PrimeFactorUnimodality.Tests
