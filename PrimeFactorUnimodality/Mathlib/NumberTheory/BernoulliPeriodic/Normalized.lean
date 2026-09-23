/-
Copyright (c) 2026 Jonas Whidden.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonas Whidden
-/
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.NumberTheory.BernoulliPolynomials

/-! # Periodic Bernoulli kernels: normalized

Extracted from Jonas Whidden's Apache-2.0 `WIPResearch`, commit
`bdc46941c4f2e13fb84e0a338b905bb10e711357`, `RobinBV/Mathlib/NumberTheory/BernoulliPeriodic.lean`.
The original `Polynomial` declaration names are retained. Only Mathlib
dependencies are used; the finite boundary terms and complete improper
tail are preserved. This module is an analytic identity, not a zero-location
assumption or numerical certificate.
-/

set_option autoImplicit false

namespace Polynomial
/-- The rational Bernoulli polynomial divided by its factorial. -/
noncomputable def bernoulliNormalized (k : Nat) : Polynomial Rat :=
  C (1/(k.factorial : Rat))*bernoulli k

/-- Differentiation lowers the normalized Bernoulli index by one. -/
theorem derivative_bernoulliNormalized (k : Nat) :
    derivative (bernoulliNormalized (k+1)) = bernoulliNormalized k := by
  have hfac : (1/((k+1).factorial : Rat))*((k : Rat)+1) = 1/(k.factorial : Rat) := by
    have hk0 : Not ((k.factorial : Rat) = 0) := by exact_mod_cast Nat.factorial_ne_zero k
    have hk1 : Not ((k : Rat)+1 = 0) := by positivity
    rw [Nat.factorial_succ]
    push_cast
    field_simp
  calc
    _ = (C (1/((k+1).factorial : Rat))*C ((k : Rat)+1))*bernoulli k := by
      simp only [bernoulliNormalized, derivative_mul, derivative_C, zero_mul,
        zero_add, derivative_bernoulli_add_one, map_add, map_natCast, map_one]
      ring
    _ = bernoulliNormalized k := by
      rw [<- C_mul, hfac]
      rfl

/-- For indices other than one, the values at the two unit endpoints agree. -/
theorem bernoulliNormalized_one_eq_zero {k : Nat} (hk : Not (k = 1)) :
    (bernoulliNormalized k).eval 1 = (bernoulliNormalized k).eval 0 := by
  simp only [bernoulliNormalized, eval_mul, eval_C, bernoulli_eval_one,
    bernoulli_eval_zero, bernoulli_eq_bernoulli'_of_ne_one hk]

/-- The normalized Bernoulli polynomial evaluated over the reals. -/
noncomputable def bernoulliNormalizedReal (k : Nat) (u : Real) : Real :=
  ((bernoulliNormalized k).map (Rat.castHom Real)).eval u

/-- The real normalized profiles have the expected successive derivatives. -/
theorem hasDerivAt_bernoulliNormalizedReal (k : Nat) (u : Real) :
    HasDerivAt (bernoulliNormalizedReal (k+1)) (bernoulliNormalizedReal k u) u := by
  change HasDerivAt (fun v : Real =>
    ((bernoulliNormalized (k+1)).map (Rat.castHom Real)).eval v)
    (((bernoulliNormalized k).map (Rat.castHom Real)).eval u) u
  simpa only [derivative_map, derivative_bernoulliNormalized] using!
    (((bernoulliNormalized (k+1)).map (Rat.castHom Real)).hasDerivAt u)

/-- The real profile has equal endpoint values away from index one. -/
theorem bernoulliNormalizedReal_one_eq_zero {k : Nat} (hk : Not (k = 1)) :
    bernoulliNormalizedReal k 1 = bernoulliNormalizedReal k 0 := by
  have h1 := eval_map_apply (p := bernoulliNormalized k) (f := Rat.castHom Real) (1 : Rat)
  have h0 := eval_map_apply (p := bernoulliNormalized k) (f := Rat.castHom Real) (0 : Rat)
  simp only [map_one, map_zero] at h1 h0
  change ((bernoulliNormalized k).map (Rat.castHom Real)).eval 1 =
    ((bernoulliNormalized k).map (Rat.castHom Real)).eval 0
  rw [h1, h0, bernoulliNormalized_one_eq_zero hk]

/-- Each real normalized profile is continuous. -/
theorem continuous_bernoulliNormalizedReal (k : Nat) :
    Continuous (bernoulliNormalizedReal k) := by
  exact (show Differentiable Real (bernoulliNormalizedReal k) from
    fun u => (((bernoulliNormalized k).map (Rat.castHom Real)).hasDerivAt u).differentiableAt).continuous

/-- Exact integration by parts for a normalized profile on one positive cell. -/
theorem bernoulliNormalizedReal_cpow_cell {k : Nat} (hk : 1 <= k)
    {a : Real} (ha : 0 < a) {z : Complex} (hz : z.re < 0) :
    intervalIntegral (fun u : Real =>
      Complex.ofReal (bernoulliNormalizedReal k u)*Complex.ofReal (a+u)^z)
      0 1 MeasureTheory.volume =
    Complex.ofReal (bernoulliNormalizedReal (k+1) 0)*
      (Complex.ofReal (a+1)^z-Complex.ofReal a^z) -
    z*intervalIntegral (fun u : Real =>
      Complex.ofReal (bernoulliNormalizedReal (k+1) u)*Complex.ofReal (a+u)^(z-1))
      0 1 MeasureTheory.volume := by
  have hz0 : Not (z = 0) := by
    intro heq
    rw [heq] at hz
    norm_num at hz
  have hcont (w : Complex) :
      ContinuousOn (fun u : Real => Complex.ofReal (a+u)^w) (Set.Icc (0 : Real) 1) := by
    have hb : Continuous (fun u : Real => Complex.ofReal (a+u)) := by fun_prop
    exact hb.continuousOn.cpow_const (fun u hu =>
      Complex.ofReal_mem_slitPlane.mpr (by linarith [hu.1]))
  have hf (u : Real) (hu : (Set.uIcc (0 : Real) 1) u) :
      HasDerivAt (fun v : Real => Complex.ofReal (a+v)^z)
        (z*Complex.ofReal (a+u)^(z-1)) u := by
    rw [Set.uIcc_of_le (by norm_num : (0 : Real) <= 1)] at hu
    have hau : 0 < a+u := by linarith [hu.1]
    have ht := hasDerivAt_ofReal_cpow_const hau.ne' hz0
    simpa only [Function.comp_def, one_smul] using!
      ht.scomp u ((hasDerivAt_id u).const_add a)
  have hq (u : Real) (_hu : (Set.uIcc (0 : Real) 1) u) :
      HasDerivAt (fun v : Real => Complex.ofReal (bernoulliNormalizedReal (k+1) v))
        (Complex.ofReal (bernoulliNormalizedReal k u)) u :=
    (hasDerivAt_bernoulliNormalizedReal k u).ofReal_comp
  have hfInt : IntervalIntegrable
      (fun u : Real => z*Complex.ofReal (a+u)^(z-1)) MeasureTheory.volume 0 1 :=
    ((hcont (z-1)).const_mul z).intervalIntegrable_of_Icc (by norm_num)
  have hpInt : IntervalIntegrable
      (fun u : Real => Complex.ofReal (bernoulliNormalizedReal k u))
      MeasureTheory.volume 0 1 :=
    (Complex.continuous_ofReal.comp (continuous_bernoulliNormalizedReal k)).intervalIntegrable 0 1
  have h := intervalIntegral.integral_mul_deriv_eq_deriv_mul hf hq hfInt hpInt
  have hleft : intervalIntegral (fun u : Real =>
      Complex.ofReal (a+u)^z*Complex.ofReal (bernoulliNormalizedReal k u))
      0 1 MeasureTheory.volume =
    intervalIntegral (fun u : Real =>
      Complex.ofReal (bernoulliNormalizedReal k u)*Complex.ofReal (a+u)^z)
      0 1 MeasureTheory.volume := by
    apply intervalIntegral.integral_congr
    intro u hu
    exact mul_comm _ _
  have hright : intervalIntegral (fun u : Real =>
      (z*Complex.ofReal (a+u)^(z-1))*Complex.ofReal (bernoulliNormalizedReal (k+1) u))
      0 1 MeasureTheory.volume =
    z*intervalIntegral (fun u : Real =>
      Complex.ofReal (bernoulliNormalizedReal (k+1) u)*Complex.ofReal (a+u)^(z-1))
      0 1 MeasureTheory.volume := by
    calc
      _ = intervalIntegral (fun u : Real => z*
          (Complex.ofReal (bernoulliNormalizedReal (k+1) u)*Complex.ofReal (a+u)^(z-1)))
          0 1 MeasureTheory.volume := by
        apply intervalIntegral.integral_congr
        intro u hu
        ring
      _ = _ := intervalIntegral.integral_const_mul z _
  rw [hleft, hright] at h
  have hend : bernoulliNormalizedReal (k+1) 1 = bernoulliNormalizedReal (k+1) 0 :=
    bernoulliNormalizedReal_one_eq_zero (by omega)
  simp only [hend, add_zero] at h
  calc
    _ = Complex.ofReal (a+1)^z*Complex.ofReal (bernoulliNormalizedReal (k+1) 0) -
        Complex.ofReal a^z*Complex.ofReal (bernoulliNormalizedReal (k+1) 0) -
        z*intervalIntegral (fun u : Real =>
          Complex.ofReal (bernoulliNormalizedReal (k+1) u)*Complex.ofReal (a+u)^(z-1))
          0 1 MeasureTheory.volume := h
    _ = _ := by ring

end Polynomial
