/-
Copyright (c) 2026 Jonas Whidden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonas Whidden
-/
import PrimeFactorUnimodality.Mathlib.Analysis.SpecialFunctions.Integrals.ReciprocalSquarePair

/-! # Exact logarithmic integrals against paired reciprocal squares

An explicit primitive evaluates the main logarithmic integral in a
positive-height zero-tail estimate. The endpoint formula uses only real
logarithms and rational operations. Integrability is proved for every
positive lower endpoint and logarithm scale, including where the
integrand changes sign.
-/

namespace Real

noncomputable section

open Filter MeasureTheory Set
open scoped Topology

/-- A fixed translation of the logarithm and denominator preserves logarithmic decay. -/
theorem tendsto_log_add_div_add_atTop (a b : ℝ) :
    Tendsto (fun x : ℝ => Real.log (x + a) / (x + b)) atTop (𝓝 0) := by
  have h := (tendsto_pow_log_div_mul_add_atTop 1 (b - a) 1 one_ne_zero).comp
    (tendsto_atTop_add_const_right atTop a tendsto_id)
  convert h using 1
  funext x
  simp only [Function.comp_apply, id_eq, pow_one, one_mul]
  rw [show x + a + (b - a) = x + b by ring]

private def logPairPrimitive (t c x : ℝ) : ℝ :=
  -(Real.log (x + t) - c) * (1 / x + 1 / (x + 2 * t)) -
    (Real.log (x + 2 * t) - Real.log x) / t

private theorem hasDerivAt_logPairPrimitive {t c x : ℝ} (ht : 0 < t) (hx : 0 < x) :
    HasDerivAt (logPairPrimitive t c)
      ((Real.log (x + t) - c) * reciprocalSquarePair t (x + t)) x := by
  have hx₁ : x + t ≠ 0 := by linarith
  have hx₂ : x + 2 * t ≠ 0 := by linarith
  have hL : HasDerivAt (fun y : ℝ => Real.log (y + t) - c) (1 / (x + t)) x := by
    simpa using (((hasDerivAt_id x).add_const t).log hx₁).sub_const c
  have hA : HasDerivAt (fun y : ℝ => 1 / y + 1 / (y + 2 * t))
      (-(1 / x ^ 2) - 1 / (x + 2 * t) ^ 2) x := by
    convert (hasDerivAt_inv hx.ne').add (((hasDerivAt_id x).add_const (2 * t)).inv hx₂) using 1
    · funext y
      simp [one_div]
    · simp only [id_eq]
      ring
  have hB : HasDerivAt (fun y : ℝ => Real.log (y + 2 * t) - Real.log y)
      (1 / (x + 2 * t) - 1 / x) x := by
    convert (((hasDerivAt_id x).add_const (2 * t)).log hx₂).sub
      ((hasDerivAt_id x).log hx.ne') using 1
    · funext y
      rfl
    · simp
  rw [reciprocalSquarePair_add]
  convert (hL.mul hA).neg.sub (hB.div_const t) using 1
  · funext y
    simp only [logPairPrimitive, Pi.sub_apply, Pi.neg_apply, Pi.mul_apply]
    ring
  · field_simp [hx.ne', hx₁, hx₂, ht.ne']
    ring

private theorem tendsto_logPairPrimitive (t c : ℝ) :
    Tendsto (logPairPrimitive t c) atTop (𝓝 0) := by
  have hquot (b : ℝ) :
      Tendsto (fun x : ℝ => (Real.log (x + t) - c) / (x + b)) atTop (𝓝 0) := by
    have hconst : Tendsto (fun x : ℝ => c / (x + b)) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop (tendsto_atTop_add_const_right atTop b tendsto_id)
    simpa only [sub_div, sub_zero] using (tendsto_log_add_div_add_atTop t b).sub hconst
  have hlog := (tendsto_log_comp_add_sub_log (2 * t)).div_const t
  convert ((hquot 0).add (hquot (2 * t))).neg.sub hlog using 1
  · funext x
    simp only [logPairPrimitive, add_zero]
    ring
  · simp

/-- The translated pair is integrable above every positive cutoff. -/
theorem integrableOn_reciprocalSquarePair_add {t H : ℝ} (ht : 0 ≤ t) (hH : 0 < H) :
    IntegrableOn (fun x => reciprocalSquarePair t (x + t)) (Ioi H) := by
  apply ((integrableOn_inv_sq_Ioi hH).const_mul 2).mono'
    (by apply Measurable.aestronglyMeasurable; unfold reciprocalSquarePair; fun_prop)
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  have hx₀ : 0 < x := hH.trans hx
  rw [Real.norm_eq_abs, abs_of_nonneg (reciprocalSquarePair_pos ht (by linarith)).le,
    reciprocalSquarePair_add]
  have hden : x ^ 2 ≤ (x + 2 * t) ^ 2 := by nlinarith
  have h := div_le_div_of_nonneg_left zero_le_one (sq_pos_of_pos hx₀) hden
  simp only [div_eq_mul_inv, one_mul] at h ⊢
  linarith

/-- Arbitrary real logarithmic offsets are allowed, even with a change of sign near the cutoff. -/
theorem integrableOn_log_sub_reciprocalSquarePair_add {t H : ℝ}
    (ht : 0 < t) (hH : 0 < H) (c : ℝ) :
    IntegrableOn (fun x => (Real.log (x + t) - c) * reciprocalSquarePair t (x + t)) (Ioi H) := by
  have hbase : IntegrableOn
      (fun x => (Real.log (x + t) - Real.log (H + t)) * reciprocalSquarePair t (x + t))
      (Ioi H) := by
    apply integrableOn_Ioi_deriv_of_nonneg'
      (fun x hx => hasDerivAt_logPairPrimitive ht (hH.trans_le hx))
      _ (tendsto_logPairPrimitive t (Real.log (H + t)))
    intro x hx
    have hx₀ : H < x := hx
    apply mul_nonneg
    · exact sub_nonneg.mpr (Real.log_le_log (by linarith) (by linarith))
    · exact (reciprocalSquarePair_pos ht.le (by linarith)).le
  apply (hbase.add ((integrableOn_reciprocalSquarePair_add ht.le hH).const_mul
    (Real.log (H + t) - c))).congr_fun _ measurableSet_Ioi
  intro x _
  simp only [Pi.add_apply]
  ring

/-- Closed-form logarithmic pair integral, with no sign restriction on the logarithmic offset. -/
theorem integral_log_sub_reciprocalSquarePair_add {t H : ℝ}
    (ht : 0 < t) (hH : 0 < H) (c : ℝ) :
    (∫ x in Ioi H, (Real.log (x + t) - c) * reciprocalSquarePair t (x + t)) =
      (Real.log (H + t) - c) * (1 / H + 1 / (H + 2 * t)) +
        (Real.log (H + 2 * t) - Real.log H) / t := by
  rw [integral_Ioi_of_hasDerivAt_of_tendsto'
    (fun x hx => hasDerivAt_logPairPrimitive ht (hH.trans_le hx))
    (integrableOn_log_sub_reciprocalSquarePair_add ht hH c) (tendsto_logPairPrimitive t c)]
  unfold logPairPrimitive
  ring

/-- The ratio form is integrable for every positive logarithm scale. -/
theorem integrableOn_log_div_reciprocalSquarePair_add {t H a : ℝ}
    (ht : 0 < t) (hH : 0 < H) (ha : 0 < a) :
    IntegrableOn (fun x => Real.log ((x + t) / a) * reciprocalSquarePair t (x + t))
      (Ioi H) := by
  apply (integrableOn_log_sub_reciprocalSquarePair_add ht hH (Real.log a)).congr_fun
    _ measurableSet_Ioi
  intro x hx
  dsimp only
  rw [Real.log_div (by have : H < x := hx; linarith) ha.ne']

/-- Logarithm-of-ratio form of the exact integral, suitable for explicit tail constants. -/
theorem integral_log_div_reciprocalSquarePair_add {t H a : ℝ}
    (ht : 0 < t) (hH : 0 < H) (ha : 0 < a) :
    (∫ x in Ioi H, Real.log ((x + t) / a) * reciprocalSquarePair t (x + t)) =
      Real.log ((H + t) / a) * (1 / H + 1 / (H + 2 * t)) +
        Real.log ((H + 2 * t) / H) / t := by
  have he : (∫ x in Ioi H, Real.log ((x + t) / a) * reciprocalSquarePair t (x + t)) =
      ∫ x in Ioi H, (Real.log (x + t) - Real.log a) * reciprocalSquarePair t (x + t) := by
    apply setIntegral_congr_fun measurableSet_Ioi
    intro x hx
    dsimp only
    rw [Real.log_div (by have : H < x := hx; linarith) ha.ne']
  rw [he, integral_log_sub_reciprocalSquarePair_add ht hH,
    Real.log_div (by linarith : H + t ≠ 0) ha.ne',
    Real.log_div (by linarith : H + 2 * t ≠ 0) hH.ne']

end

end Real
