/-
Copyright (c) 2026 Jonas Whidden.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonas Whidden
-/
import PrimeFactorUnimodality.Mathlib.NumberTheory.BernoulliPeriodic.Integrability

/-! # Periodic Bernoulli kernels: cells

Extracted from Jonas Whidden's Apache-2.0 `WIPResearch`, commit
`bdc46941c4f2e13fb84e0a338b905bb10e711357`, `RobinBV/Mathlib/NumberTheory/BernoulliPeriodic.lean`.
The original `Polynomial` declaration names are retained. Only Mathlib
dependencies are used; the finite boundary terms and complete improper
tail are preserved. This module is an analytic identity, not a zero-location
assumption or numerical certificate.
-/

set_option autoImplicit false

namespace Polynomial
/-- Integer translation identifies a periodic cell integral with its unit profile. -/
theorem bernoulliPeriodic_cpow_unit_shift (k N : Nat) (z : Complex) :
    intervalIntegral (fun x : Real =>
      Complex.ofReal (bernoulliPeriodic k x)*Complex.ofReal x^z)
      (N : Real) ((N : Real)+1) MeasureTheory.volume =
    intervalIntegral (fun u : Real =>
      Complex.ofReal (bernoulliNormalizedReal k u)*Complex.ofReal ((N : Real)+u)^z)
      0 1 MeasureTheory.volume := by
  calc
    _ = intervalIntegral (fun u : Real =>
        Complex.ofReal (bernoulliPeriodic k ((N : Real)+u))*Complex.ofReal ((N : Real)+u)^z)
        0 1 MeasureTheory.volume := by
      simpa only [add_zero] using
        (intervalIntegral.integral_comp_add_left (a := (0 : Real)) (b := 1)
          (fun x : Real => Complex.ofReal (bernoulliPeriodic k x)*Complex.ofReal x^z)
          (N : Real)).symm
    _ = _ := by
      apply intervalIntegral.integral_congr_ae
      have hne : Filter.Eventually (fun x : Real => Not (x = 1))
          (MeasureTheory.ae MeasureTheory.volume) := by
        simp [MeasureTheory.ae_iff]
      filter_upwards [hne] with u hu
      intro hmem
      rw [Set.uIoc_of_le (by norm_num : (0 : Real) <= 1)] at hmem
      have hu1 : u < 1 := lt_of_le_of_ne hmem.2 hu
      have hfrac : Int.fract ((N : Real)+u) = u := by
        rw [add_comm, Int.fract_add_natCast,
          Int.fract_eq_self.mpr (And.intro hmem.1.le hu1)]
      simp only [bernoulliPeriodic, hfrac]

/-- The periodic power integral satisfies the exact one-cell recursion. -/
theorem bernoulliPeriodic_cpow_cell {k N : Nat} (hk : 1 <= k) (hN : 0 < N)
    {z : Complex} (hz : z.re < 0) :
    intervalIntegral (fun x : Real =>
      Complex.ofReal (bernoulliPeriodic k x)*Complex.ofReal x^z)
      (N : Real) ((N : Real)+1) MeasureTheory.volume =
    Complex.ofReal (bernoulliNormalizedReal (k+1) 0)*
      (Complex.ofReal ((N : Real)+1)^z-Complex.ofReal (N : Real)^z) -
    z*intervalIntegral (fun x : Real =>
      Complex.ofReal (bernoulliPeriodic (k+1) x)*Complex.ofReal x^(z-1))
      (N : Real) ((N : Real)+1) MeasureTheory.volume := by
  rw [bernoulliPeriodic_cpow_unit_shift k N z,
    bernoulliPeriodic_cpow_unit_shift (k+1) N (z-1)]
  exact bernoulliNormalizedReal_cpow_cell hk (by exact_mod_cast hN) hz

/-- Adjacent positive integer cells telescope with both boundary terms retained. -/
theorem bernoulliPeriodic_cpow_finite_recursion {k N : Nat} (hk : 1 <= k)
    (hN : 0 < N) {z : Complex} (hz : z.re < -1) (M : Nat) :
    intervalIntegral (fun x : Real =>
      Complex.ofReal (bernoulliPeriodic k x)*Complex.ofReal x^z)
      (N : Real) ((N : Real)+(M : Real)) MeasureTheory.volume =
    Complex.ofReal (bernoulliNormalizedReal (k+1) 0)*
      (Complex.ofReal ((N : Real)+(M : Real))^z-Complex.ofReal (N : Real)^z) -
    z*intervalIntegral (fun x : Real =>
      Complex.ofReal (bernoulliPeriodic (k+1) x)*Complex.ofReal x^(z-1))
      (N : Real) ((N : Real)+(M : Real)) MeasureTheory.volume := by
  have hN0 : (0 : Real) < N := by exact_mod_cast hN
  have hz1 : (z-1).re < -1 := by
    rw [Complex.sub_re, Complex.one_re]
    linarith
  have hInt (j : Nat) (w : Complex) (hw : w.re < -1) (a b : Real)
      (ha : (N : Real) <= a) (hab : a <= b) :
      IntervalIntegrable
        (fun x : Real => Complex.ofReal (bernoulliPeriodic j x)*Complex.ofReal x^w)
        MeasureTheory.volume a b := by
    have hsmall := ((bernoulliPeriodic_cpow_tail_bound j).choose_spec.2
      ((N : Real)/2) w (by positivity) hw).1
    have hpart : MeasureTheory.IntegrableOn
        (fun x : Real => Complex.ofReal (bernoulliPeriodic j x)*Complex.ofReal x^w)
        (Set.uIcc a b) := by
      apply hsmall.mono_set
      intro x hx
      rw [Set.uIcc_of_le hab] at hx
      change (N : Real)/2 < x
      linarith [hx.1]
    exact hpart.intervalIntegrable
  induction M with
  | zero =>
    simp only [Nat.cast_zero, add_zero, intervalIntegral.integral_same,
      sub_self, mul_zero]
  | succ M ih =>
    have hNM : (N : Real) <= (N : Real)+(M : Real) :=
      le_add_of_nonneg_right (Nat.cast_nonneg M)
    have hF := intervalIntegral.integral_add_adjacent_intervals
      (hInt k z hz (N : Real) ((N : Real)+(M : Real)) (le_refl _) hNM)
      (hInt k z hz ((N : Real)+(M : Real)) ((N : Real)+((M : Real)+1)) hNM (by linarith))
    have hG := intervalIntegral.integral_add_adjacent_intervals
      (hInt (k+1) (z-1) hz1 (N : Real) ((N : Real)+(M : Real)) (le_refl _) hNM)
      (hInt (k+1) (z-1) hz1 ((N : Real)+(M : Real))
        ((N : Real)+((M : Real)+1)) hNM (by linarith))
    have hcell := bernoulliPeriodic_cpow_cell hk
      (show 0 < N+M by omega) (show z.re < 0 by linarith)
    simp only [Nat.cast_add, add_assoc] at hcell
    simp only [Nat.cast_succ]
    rw [<- hF, <- hG, ih, hcell]
    ring

end Polynomial
