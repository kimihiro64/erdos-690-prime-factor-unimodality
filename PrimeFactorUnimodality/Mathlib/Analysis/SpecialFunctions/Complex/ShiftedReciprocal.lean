/-
Copyright (c) 2026 Jonas Whidden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonas Whidden
-/
import Mathlib.Analysis.Calculus.Deriv.ZPow
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-! # Reciprocal powers on horizontal right-half-plane rays

Natural reciprocal powers have explicit derivatives and integrable norm
tails. The real-part bound is used for convergence, not as a claim that
high-precision numerical remainders must ignore the imaginary part.
-/

open MeasureTheory Set
open scoped Topology

namespace Complex

/-- A nonnegative horizontal displacement preserves nonvanishing in the right half-plane. -/
theorem add_ofReal_ne_zero_of_re_pos {z : ℂ} {x : ℝ} (hz : 0 < z.re) (hx : 0 ≤ x) :
    z + (x : ℂ) ≠ 0 := by
  have hp : 0 < (z + (x : ℂ)).re := by simp only [add_re, ofReal_re]; linarith
  intro he
  simp [he] at hp

/-- The derivative of a natural reciprocal power along a horizontal segment. -/
theorem hasDerivAt_inv_pow_add_ofReal (p : ℕ) {z : ℂ} {x : ℝ} (hx : z + (x : ℂ) ≠ 0) :
    HasDerivAt (fun y : ℝ => (z + (y : ℂ))⁻¹ ^ p)
      (-(p : ℂ) * (z + (x : ℂ))⁻¹ ^ (p + 1)) x := by
  have hd := ((hasDerivAt_zpow (-(p : ℤ)) (z + (x : ℂ)) (Or.inl hx)).comp (x : ℂ)
    ((hasDerivAt_id (x : ℂ)).const_add z)).comp_ofReal
  have he : -(p : ℤ) - 1 = -((p + 1 : ℕ) : ℤ) := by omega
  simpa only [he, Function.comp_def, zpow_neg, zpow_natCast, inv_pow, Int.cast_neg,
    Int.cast_natCast, mul_one] using hd

/-- Continuity of reciprocal powers on the complete positive ray. -/
theorem continuousOn_inv_pow_add_ofReal (p : ℕ) {z : ℂ} (hz : 0 < z.re) :
    ContinuousOn (fun x : ℝ => (z + (x : ℂ))⁻¹ ^ p) (Ici 0) := by
  exact (((continuous_const.add continuous_ofReal).continuousOn).inv₀
    (fun x hx => add_ofReal_ne_zero_of_re_pos hz hx)).pow p

/-- The real part bounds the absolute reciprocal power at each point of the positive ray. -/
theorem norm_inv_pow_add_ofReal_le (p : ℕ) {z : ℂ} {x : ℝ}
    (hz : 0 < z.re) (hx : 0 ≤ x) :
    ‖(z + (x : ℂ))⁻¹ ^ p‖ ≤ (z.re + x) ^ (-(p : ℝ)) := by
  have hp : 0 < z.re + x := by linarith
  have hn : z.re + x ≤ ‖z + (x : ℂ)‖ := by simpa using re_le_norm (z + (x : ℂ))
  rw [norm_pow, norm_inv, Real.rpow_neg hp.le, Real.rpow_natCast, ← inv_pow]
  exact pow_le_pow_left₀ (inv_nonneg.mpr (norm_nonneg _)) (inv_anti₀ hp hn) p

/-- Reciprocal powers of order greater than one have integrable norms on the full ray. -/
theorem integrableOn_inv_pow_add_ofReal {p : ℕ} (hp : 1 < p) {z : ℂ} (hz : 0 < z.re) :
    IntegrableOn (fun x : ℝ => (z + (x : ℂ))⁻¹ ^ p) (Ioi 0) := by
  have hpR : (1 : ℝ) < p := by exact_mod_cast hp
  have hb := integrableOn_add_rpow_Ioi_of_lt (m := z.re) (c := 0)
    (by linarith : -(p : ℝ) < -1) (by linarith : -z.re < 0)
  have hcont := (continuousOn_inv_pow_add_ofReal p hz).mono Ioi_subset_Ici_self
  apply hb.mono' (hcont.aestronglyMeasurable measurableSet_Ioi)
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  simpa only [add_comm] using norm_inv_pow_add_ofReal_le p hz hx.le

/-- Every positive reciprocal power vanishes along integer translates of the ray. -/
theorem tendsto_inv_pow_add_nat {p : ℕ} (hp : 0 < p) {z : ℂ} (hz : 0 < z.re) :
    Filter.Tendsto (fun n : ℕ => (z + (n : ℂ))⁻¹ ^ p) Filter.atTop (𝓝 0) := by
  have ht : Filter.Tendsto (fun n : ℕ => z.re + (n : ℝ)) Filter.atTop Filter.atTop :=
    Filter.tendsto_atTop_mono (fun n => le_add_of_nonneg_left hz.le)
      tendsto_natCast_atTop_atTop
  have hr := (tendsto_rpow_neg_atTop (by exact_mod_cast hp : (0 : ℝ) < p)).comp ht
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  exact squeeze_zero (fun _ => norm_nonneg _)
    (fun n => by simpa using norm_inv_pow_add_ofReal_le p hz (Nat.cast_nonneg n)) hr

end Complex
