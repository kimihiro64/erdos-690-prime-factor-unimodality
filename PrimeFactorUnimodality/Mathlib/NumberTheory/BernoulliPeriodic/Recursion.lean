/-
Copyright (c) 2026 Jonas Whidden.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonas Whidden
-/
import PrimeFactorUnimodality.Mathlib.NumberTheory.BernoulliPeriodic.Cells

/-! # Periodic Bernoulli kernels: recursion

Extracted from Jonas Whidden's Apache-2.0 `WIPResearch`, commit
`bdc46941c4f2e13fb84e0a338b905bb10e711357`, `RobinBV/Mathlib/NumberTheory/BernoulliPeriodic.lean`.
The original `Polynomial` declaration names are retained. Only Mathlib
dependencies are used; the finite boundary terms and complete improper
tail are preserved. This module is an analytic identity, not a zero-location
assumption or numerical certificate.
-/

set_option autoImplicit false

namespace Polynomial
/-- The finite recursion passes to the absolutely convergent infinite tail. -/
theorem bernoulliPeriodic_cpow_tail_recursion {k N : Nat} (hk : 1 <= k)
    (hN : 0 < N) {z : Complex} (hz : z.re < -1) :
    MeasureTheory.integral (MeasureTheory.volume.restrict (Set.Ioi (N : Real)))
      (fun x : Real => Complex.ofReal (bernoulliPeriodic k x)*Complex.ofReal x^z) =
    -Complex.ofReal (bernoulliNormalizedReal (k+1) 0)*Complex.ofReal (N : Real)^z -
    z*MeasureTheory.integral (MeasureTheory.volume.restrict (Set.Ioi (N : Real)))
      (fun x : Real => Complex.ofReal (bernoulliPeriodic (k+1) x)*Complex.ofReal x^(z-1)) := by
  have hN0 : (0 : Real) < N := by exact_mod_cast hN
  have hz1 : (z-1).re < -1 := by
    rw [Complex.sub_re, Complex.one_re]
    linarith
  have hFInt := ((bernoulliPeriodic_cpow_tail_bound k).choose_spec.2
    (N : Real) z hN0 hz).1
  have hGInt := ((bernoulliPeriodic_cpow_tail_bound (k+1)).choose_spec.2
    (N : Real) (z-1) hN0 hz1).1
  have ht : Filter.Tendsto (fun m : Nat => (N : Real)+(m : Real))
      Filter.atTop Filter.atTop :=
    Filter.tendsto_atTop_mono
      (fun m : Nat => le_add_of_nonneg_left hN0.le) tendsto_natCast_atTop_atTop
  have hpow : Filter.Tendsto (fun m : Nat => Complex.ofReal ((N : Real)+(m : Real))^z)
      Filter.atTop (nhds 0) := by
    have hr : Filter.Tendsto (fun m : Nat => ((N : Real)+(m : Real))^z.re)
        Filter.atTop (nhds 0) := by
      simpa only [neg_neg, Function.comp_def] using
        (tendsto_rpow_neg_atTop (by linarith : 0 < -z.re)).comp ht
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    have heq : (fun m : Nat => norm (Complex.ofReal ((N : Real)+(m : Real))^z)) =
        (fun m : Nat => ((N : Real)+(m : Real))^z.re) := by
      funext m
      exact Complex.norm_cpow_eq_rpow_re_of_pos
        (by positivity : 0 < (N : Real)+(m : Real)) z
    rw [heq]
    exact hr
  have hlimF := MeasureTheory.intervalIntegral_tendsto_integral_Ioi (N : Real) hFInt ht
  have hlimG := MeasureTheory.intervalIntegral_tendsto_integral_Ioi (N : Real) hGInt ht
  have hlimR := ((hpow.sub_const (Complex.ofReal (N : Real)^z)).const_mul
    (Complex.ofReal (bernoulliNormalizedReal (k+1) 0))).sub (hlimG.const_mul z)
  have hfun : (fun m : Nat =>
      Complex.ofReal (bernoulliNormalizedReal (k+1) 0)*
        (Complex.ofReal ((N : Real)+(m : Real))^z-Complex.ofReal (N : Real)^z) -
      z*intervalIntegral (fun x : Real =>
        Complex.ofReal (bernoulliPeriodic (k+1) x)*Complex.ofReal x^(z-1))
        (N : Real) ((N : Real)+(m : Real)) MeasureTheory.volume) =
    (fun m : Nat => intervalIntegral (fun x : Real =>
      Complex.ofReal (bernoulliPeriodic k x)*Complex.ofReal x^z)
      (N : Real) ((N : Real)+(m : Real)) MeasureTheory.volume) := by
    funext m
    exact (bernoulliPeriodic_cpow_finite_recursion hk hN hz m).symm
  change Filter.Tendsto (fun m : Nat =>
    Complex.ofReal (bernoulliNormalizedReal (k+1) 0)*
      (Complex.ofReal ((N : Real)+(m : Real))^z-Complex.ofReal (N : Real)^z) -
    z*intervalIntegral (fun x : Real =>
      Complex.ofReal (bernoulliPeriodic (k+1) x)*Complex.ofReal x^(z-1))
      (N : Real) ((N : Real)+(m : Real)) MeasureTheory.volume)
    Filter.atTop
    (nhds (Complex.ofReal (bernoulliNormalizedReal (k+1) 0)*
      (0-Complex.ofReal (N : Real)^z) -
      z*MeasureTheory.integral (MeasureTheory.volume.restrict (Set.Ioi (N : Real)))
        (fun x : Real => Complex.ofReal (bernoulliPeriodic (k+1) x)*Complex.ofReal x^(z-1))))
    at hlimR
  rw [hfun] at hlimR
  have heq := tendsto_nhds_unique hlimF hlimR
  simpa only [zero_sub, mul_neg, neg_mul] using heq

end Polynomial
