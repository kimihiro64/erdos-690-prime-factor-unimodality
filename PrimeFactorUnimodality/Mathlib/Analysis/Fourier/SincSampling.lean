/-
Copyright (c) 2026 Jonas Whidden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonas Whidden
-/
import Mathlib.Analysis.Fourier.Inversion
import Mathlib.Analysis.Fourier.PoissonSummation
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-! # Sinc sampling as the inverse integral of the aliased Fourier transform

Absolute convergence of the time samples justifies integration of their
Fourier series. Poisson summation identifies that series with the aliased
transform. No band-limit hypothesis is imposed.
-/

open MeasureTheory Filter Asymptotics TopologicalSpace
open scoped FourierTransform

namespace Fourier

noncomputable section

/-- The unit-modulus phase in the inverse real Fourier integral. -/
def samplingPhase (t x : ℝ) : ℂ := Complex.exp ((2 * Real.pi * t * x : ℝ) * Complex.I)

@[simp] theorem norm_samplingPhase (t x : ℝ) : ‖samplingPhase t x‖ = 1 := by
  simp only [samplingPhase, Complex.norm_exp, Complex.mul_re, Complex.ofReal_re,
    Complex.I_re, Complex.ofReal_im, Complex.I_im, mul_zero, zero_mul,
    sub_zero, Real.exp_zero]

theorem continuous_samplingPhase (t : ℝ) : Continuous (samplingPhase t) := by
  unfold samplingPhase
  fun_prop

/-- Modulation translates the actual Fourier integral, with the negative modulation sign. -/
theorem fourier_samplingPhase_neg_mul (f : ℝ → ℂ) (x y : ℝ) :
    𝓕 (fun t => samplingPhase (-x) t * f t) y = 𝓕 f (x + y) := by
  simp only [Real.fourier_real_eq_integral_exp_smul, smul_eq_mul, samplingPhase]
  apply integral_congr_ae
  filter_upwards with t
  rw [← mul_assoc, ← Complex.exp_add]
  congr 2
  push_cast
  ring

/-- The normalized sinc kernel is exactly the integral over the central unit frequency cell. -/
theorem integral_samplingPhase (t : ℝ) :
    (∫ x in (-1 / 2 : ℝ)..(1 / 2 : ℝ), samplingPhase t x) =
      (Real.sinc (Real.pi * t) : ℂ) := by
  by_cases ht : t = 0
  · norm_num [ht, samplingPhase]
  have hc : 2 * Real.pi * t ≠ 0 :=
    mul_ne_zero (mul_ne_zero (by norm_num) Real.pi_ne_zero) ht
  have he (x : ℝ) : samplingPhase t x =
      Complex.exp (((2 * Real.pi * t) * x : ℝ) * Complex.I) := rfl
  simp_rw [he]
  rw [intervalIntegral.integral_comp_mul_left
    (fun x : ℝ => Complex.exp ((x : ℂ) * Complex.I)) hc]
  rw [show (2 * Real.pi * t) * (-1 / 2) = -(Real.pi * t) by ring,
    show (2 * Real.pi * t) * (1 / 2) = Real.pi * t by ring,
    integral_exp_mul_I_eq_sinc]
  simp only [Complex.real_smul, Complex.ofReal_inv, Complex.ofReal_mul, Complex.ofReal_ofNat]
  field_simp [Complex.ofReal_ne_zero.mpr ht]

/-- The modulation does not change a norm decay hypothesis. -/
theorem isBigO_samplingPhase_mul {f : ℝ → ℂ} {g : ℝ → ℝ} {l : Filter ℝ}
    (hf : f =O[l] g) (x : ℝ) : (fun t => samplingPhase x t * f t) =O[l] g := by
  apply (isBigO_of_le l ?_).trans hf
  intro t
  simp

/-- Poisson summation in the form required for interpolation from integer samples. -/
theorem tsum_fourier_shift_eq_samples {f : ℝ → ℂ} (hc : Continuous f) {b : ℝ}
    (hb : 1 < b) (hf : f =O[cocompact ℝ] (fun t => |t| ^ (-b))) (x : ℝ)
    (hF : Summable (fun n : ℤ => 𝓕 f (x + n))) :
    (∑' n : ℤ, 𝓕 f (x + n)) = ∑' n : ℤ, samplingPhase (-(n : ℝ)) x * f n := by
  have hs : Summable (fun n : ℤ => 𝓕 (fun t => samplingPhase (-x) t * f t) n) := by
    simpa only [fourier_samplingPhase_neg_mul] using hF
  have hp := Real.tsum_eq_tsum_fourier_of_rpow_decay_of_summable
    ((continuous_samplingPhase (-x)).mul hc) hb (isBigO_samplingPhase_mul hf (-x)) hs 0
  change (∑' n : ℤ, samplingPhase (-x) (0 + n) * f (0 + n)) =
    ∑' n : ℤ, 𝓕 (fun t => samplingPhase (-x) t * f t) n *
      fourier n (0 : UnitAddCircle) at hp
  simpa only [zero_add, fourier_samplingPhase_neg_mul, AddCircle.coe_zero,
    fourier_eval_zero, mul_one,
    show ∀ n : ℤ, samplingPhase (-x) n = samplingPhase (-(n : ℝ)) x by
      intro n; unfold samplingPhase; congr 2; push_cast; ring] using hp.symm

/-- Absolute summability of samples suffices for absolute convergence of sinc interpolation. -/
theorem summable_sinc_samples {f : ℤ → ℂ} (hf : Summable (fun n => ‖f n‖)) (t : ℝ) :
    Summable (fun n : ℤ => f n * (Real.sinc (Real.pi * (t - n)) : ℂ)) := by
  apply hf.of_norm_bounded
  intro n
  simpa only [norm_mul, Complex.norm_real, Real.norm_eq_abs, mul_one] using
    mul_le_mul_of_nonneg_left (Real.abs_sinc_le_one (Real.pi * (t - n))) (norm_nonneg (f n))

/-- Interchanging the absolutely convergent Fourier series and the compact inverse integral. -/
theorem tsum_sinc_eq_integral_series {f : ℤ → ℂ}
    (hf : Summable (fun n => ‖f n‖)) (t : ℝ) :
    (∑' n : ℤ, f n * (Real.sinc (Real.pi * (t - n)) : ℂ)) =
      ∫ x in (-1 / 2 : ℝ)..(1 / 2 : ℝ),
        samplingPhase t x * ∑' n : ℤ, samplingPhase (-(n : ℝ)) x * f n := by
  let g (n : ℤ) : C(ℝ, ℂ) :=
    ⟨fun x => samplingPhase (t - n) x * f n, (continuous_samplingPhase _).mul continuous_const⟩
  have hg : Summable (fun n => ‖(g n).restrict
      (⟨Set.uIcc (-1 / 2 : ℝ) (1 / 2 : ℝ), isCompact_uIcc⟩ : Compacts ℝ)‖) := by
    apply hf.of_nonneg_of_le (fun _ => norm_nonneg _)
    intro n
    apply ContinuousMap.norm_le _ (norm_nonneg _)|>.mpr
    intro x
    simp [g]
  have he (n : ℤ) : (∫ x in (-1 / 2 : ℝ)..(1 / 2 : ℝ), g n x) =
      f n * (Real.sinc (Real.pi * (t - n)) : ℂ) := by
    change (∫ x in (-1 / 2 : ℝ)..(1 / 2 : ℝ), samplingPhase (t - n) x * f n) = _
    rw [intervalIntegral.integral_mul_const, integral_samplingPhase, mul_comm]
  calc
    _ = ∑' n : ℤ, ∫ x in (-1 / 2 : ℝ)..(1 / 2 : ℝ), g n x := (tsum_congr he).symm
    _ = ∫ x in (-1 / 2 : ℝ)..(1 / 2 : ℝ), ∑' n : ℤ, g n x :=
      intervalIntegral.tsum_intervalIntegral_eq_of_summable_norm hg
    _ = _ := by
      apply intervalIntegral.integral_congr
      intro x hx
      dsimp only
      rw [← tsum_mul_left]
      apply tsum_congr
      intro n
      change samplingPhase (t - n) x * f n =
        samplingPhase t x * (samplingPhase (-(n : ℝ)) x * f n)
      rw [← mul_assoc]
      congr 1
      unfold samplingPhase
      rw [← Complex.exp_add]
      congr 1
      push_cast
      ring

end

end Fourier
