/-
Copyright (c) 2026 Jonas Whidden.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonas Whidden
-/
import Mathlib.MeasureTheory.Function.Floor
import PrimeFactorUnimodality.Mathlib.NumberTheory.BernoulliPeriodic.Normalized

/-! # Periodic Bernoulli kernels: integrability

Extracted from Jonas Whidden's Apache-2.0 `WIPResearch`, commit
`bdc46941c4f2e13fb84e0a338b905bb10e711357`, `RobinBV/Mathlib/NumberTheory/BernoulliPeriodic.lean`.
The original `Polynomial` declaration names are retained. Only Mathlib
dependencies are used; the finite boundary terms and complete improper
tail are preserved. This module is an analytic identity, not a zero-location
assumption or numerical certificate.
-/

set_option autoImplicit false

namespace Polynomial
/-- The normalized profile extended periodically through the fractional part. -/
noncomputable def bernoulliPeriodic (k : Nat) (x : Real) : Real :=
  bernoulliNormalizedReal k (Int.fract x)

/-- The periodic Bernoulli kernel is measurable, including index one. -/
theorem measurable_bernoulliPeriodic (k : Nat) : Measurable (bernoulliPeriodic k) :=
  (continuous_bernoulliNormalizedReal k).measurable.comp measurable_fract

/-- Each periodic kernel has a uniformly bounded, absolutely integrable power tail. -/
theorem bernoulliPeriodic_cpow_tail_bound (k : Nat) :
    Exists fun C : Real => 1 <= C /\
      forall (a : Real) (z : Complex), 0 < a -> z.re < -1 ->
      MeasureTheory.IntegrableOn
        (fun x : Real => Complex.ofReal (bernoulliPeriodic k x)*Complex.ofReal x^z)
        (Set.Ioi a) /\
      norm (MeasureTheory.integral (MeasureTheory.volume.restrict (Set.Ioi a))
        (fun x : Real => Complex.ofReal (bernoulliPeriodic k x)*Complex.ofReal x^z)) <=
        C*(-a^(z.re+1)/(z.re+1)) := by
  obtain h := (isCompact_Icc (a := (0 : Real)) (b := 1)).exists_bound_of_continuousOn
    (continuous_bernoulliNormalizedReal k).continuousOn
  let C : Real := max h.choose 1
  have hB (x : Real) : norm (Complex.ofReal (bernoulliPeriodic k x)) <= C := by
    rw [Complex.norm_real]
    exact (h.choose_spec (Int.fract x)
      (And.intro (Int.fract_nonneg x) (Int.fract_lt_one x).le)).trans (le_max_left _ _)
  refine Exists.intro C (And.intro (le_max_right _ _) ?_)
  intro a z ha hz
  let mu : MeasureTheory.Measure Real := MeasureTheory.volume.restrict (Set.Ioi a)
  have hPow : MeasureTheory.Integrable (fun x : Real => Complex.ofReal x^z) mu :=
    integrableOn_Ioi_cpow_of_lt hz ha
  have hMajor : MeasureTheory.Integrable (fun x : Real => C*x^z.re) mu :=
    (integrableOn_Ioi_rpow_of_lt hz ha).const_mul C
  have hBm : Measurable (fun x : Real => Complex.ofReal (bernoulliPeriodic k x)) :=
    Complex.continuous_ofReal.measurable.comp (measurable_bernoulliPeriodic k)
  have hMeas : MeasureTheory.AEStronglyMeasurable
      (fun x : Real => Complex.ofReal (bernoulliPeriodic k x)*Complex.ofReal x^z) mu :=
    hBm.aestronglyMeasurable.mul hPow.aestronglyMeasurable
  have hBound : Filter.Eventually
      (fun x : Real => norm (Complex.ofReal (bernoulliPeriodic k x)*Complex.ofReal x^z)
        <= C*x^z.re) (MeasureTheory.ae mu) := by
    have hmem : Filter.Eventually (fun x : Real => (Set.Ioi a) x)
        (MeasureTheory.ae mu) := MeasureTheory.ae_restrict_mem measurableSet_Ioi
    filter_upwards [hmem] with x hx
    rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos (ha.trans hx)]
    exact mul_le_mul_of_nonneg_right (hB x)
      (Real.rpow_nonneg (ha.trans hx).le z.re)
  have hInt : MeasureTheory.Integrable
      (fun x : Real => Complex.ofReal (bernoulliPeriodic k x)*Complex.ofReal x^z) mu :=
    hMajor.mono' hMeas hBound
  refine And.intro hInt ?_
  calc
    _ <= MeasureTheory.integral mu
        (fun x : Real => norm (Complex.ofReal (bernoulliPeriodic k x)*Complex.ofReal x^z)) :=
      MeasureTheory.norm_integral_le_integral_norm _
    _ <= MeasureTheory.integral mu (fun x : Real => C*x^z.re) :=
      MeasureTheory.integral_mono_ae hInt.norm hMajor hBound
    _ = C*(-a^(z.re+1)/(z.re+1)) := by
      dsimp [mu]
      rw [MeasureTheory.integral_const_mul, integral_Ioi_rpow_of_lt hz ha]

end Polynomial
