/-
Copyright (c) 2026 Jonas Whidden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonas Whidden
-/
import PrimeFactorUnimodality.Mathlib.Analysis.SpecialFunctions.Integrals.LogReciprocalSquarePair
import PrimeFactorUnimodality.Mathlib.Analysis.SpecialFunctions.Integrals.ReciprocalSquarePairDeriv
import PrimeFactorUnimodality.Mathlib.MeasureTheory.Integral.IoiTranslation

/-! # Weighted bounds and logarithmic decay for the reciprocal-square pair

Uniform distance from the poles controls the negative derivative by the
pair itself, including an extra linear factor. Logarithmic and linear-log
weights still leave zero boundary terms at infinity.
-/

namespace Real

open Filter MeasureTheory Set
open scoped Topology

/-- The positive negative-derivative kernel of the paired reciprocal squares. -/
noncomputable def reciprocalSquarePairSlope (t x : ℝ) : ℝ :=
  2 / (x - t) ^ 3 + 2 / (x + t) ^ 3

/-- The slope kernel is nonnegative to the right of both poles. -/
theorem reciprocalSquarePairSlope_nonneg {t x : ℝ} (ht : 0 ≤ t) (hx : t < x) :
    0 ≤ reciprocalSquarePairSlope t x := by
  have hm : 0 < x - t := sub_pos.mpr hx
  have hp : 0 < x + t := by linarith
  unfold reciprocalSquarePairSlope
  positivity

/-- A fixed positive distance from the poles controls the derivative kernel. -/
theorem reciprocalSquarePairSlope_le {t H x : ℝ} (ht : 0 ≤ t) (hH : 0 < H)
    (hx : t + H ≤ x) : reciprocalSquarePairSlope t x ≤ (2 / H) * reciprocalSquarePair t x := by
  have hb {y : ℝ} (hy : H ≤ y) : 2 / y ^ 3 ≤ (2 / H) * (1 / y ^ 2) := by
    calc
      _ = (2 / y) * (1 / y ^ 2) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right
        (div_le_div_of_nonneg_left (by norm_num) hH hy) (by positivity)
  have hm : H ≤ x - t := by linarith
  have hp : H ≤ x + t := by linarith
  exact (add_le_add (hb hm) (hb hp)).trans_eq (by
    unfold reciprocalSquarePair
    ring)

/-- The linearly weighted derivative is also controlled by the original pair. -/
theorem mul_reciprocalSquarePairSlope_le {t H x : ℝ} (ht : 0 ≤ t) (hH : 0 < H)
    (hx : t + H ≤ x) :
    x * reciprocalSquarePairSlope t x ≤ 2 * (1 + t / H) * reciprocalSquarePair t x := by
  have hm : 0 < x - t := by linarith
  have hp : 0 < x + t := by linarith
  have hb : x / (x - t) ≤ 1 + t / H := by
    calc
      _ = 1 + t / (x - t) := by field_simp; ring
      _ ≤ _ := add_le_add le_rfl (div_le_div_of_nonneg_left ht hH (by linarith))
  have hc : x / (x + t) ≤ 1 + t / H := by
    have h₁ : x / (x + t) ≤ 1 := (div_le_one hp).mpr (by linarith)
    exact h₁.trans (le_add_of_nonneg_right (div_nonneg ht hH.le))
  have h₁ := mul_le_mul_of_nonneg_right hb (by positivity : 0 ≤ 2 / (x - t) ^ 2)
  have h₂ := mul_le_mul_of_nonneg_right hc (by positivity : 0 ≤ 2 / (x + t) ^ 2)
  convert add_le_add h₁ h₂ using 1 <;>
    simp only [reciprocalSquarePairSlope, reciprocalSquarePair, div_eq_mul_inv, ← inv_pow] <;> ring

private theorem tendsto_log_sub_div_add (b c : ℝ) :
    Tendsto (fun x : ℝ => (Real.log x - c) / (x + b)) atTop (𝓝 0) := by
  have hlog := tendsto_log_add_div_add_atTop 0 b
  have hc : Tendsto (fun x : ℝ => c / (x + b)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (tendsto_atTop_add_const_right atTop b tendsto_id)
  simpa only [add_zero, sub_div, sub_zero] using hlog.sub hc

/-- Multiplying by a logarithm preserves the zero boundary of the pair. -/
theorem tendsto_log_sub_mul_reciprocalSquarePair_atTop (t c : ℝ) :
    Tendsto (fun x => (Real.log x - c) * reciprocalSquarePair t x) atTop (𝓝 0) := by
  have h (b : ℝ) : Tendsto (fun x : ℝ => (Real.log x - c) / (x + b) ^ 2) atTop (𝓝 0) := by
    have hi : Tendsto (fun x : ℝ => 1 / (x + b)) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop (tendsto_atTop_add_const_right atTop b tendsto_id)
    convert (tendsto_log_sub_div_add b c).mul hi using 1
    · funext x
      simp only [div_eq_mul_inv, ← inv_pow]
      ring
    · simp
  convert (h (-t)).add (h t) using 1
  · funext x
    unfold reciprocalSquarePair
    ring
  · simp

/-- Even a linear-log weight leaves a zero boundary at infinity. -/
theorem tendsto_mul_log_sub_mul_reciprocalSquarePair_atTop (t c : ℝ) :
    Tendsto (fun x => x * (Real.log x - c) * reciprocalSquarePair t x) atTop (𝓝 0) := by
  have hr (b : ℝ) : Tendsto (fun x : ℝ => x / (x + b)) atTop (𝓝 1) := by
    have hb : Tendsto (fun x : ℝ => b / (x + b)) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop (tendsto_atTop_add_const_right atTop b tendsto_id)
    have h := hb.const_sub 1
    simp only [sub_zero] at h
    apply h.congr'
    filter_upwards [eventually_gt_atTop (-b)] with x hx
    have hn : x + b ≠ 0 := by linarith
    field_simp
    ring
  have h (b : ℝ) : Tendsto (fun x : ℝ => x * (Real.log x - c) / (x + b) ^ 2)
      atTop (𝓝 0) := by
    convert (hr b).mul (tendsto_log_sub_div_add b c) using 1
    · funext x
      simp only [div_eq_mul_inv, ← inv_pow]
      ring
    · simp
  convert (h (-t)).add (h t) using 1
  · funext x
    unfold reciprocalSquarePair
    ring
  · simp

/-- Logarithmic derivative weights are absolutely integrable above any positive pole gap. -/
theorem integrableOn_log_sub_mul_reciprocalSquarePairSlope {t H : ℝ}
    (ht : 0 < t) (hH : 0 < H) (c : ℝ) :
    IntegrableOn (fun x => (Real.log x - c) * reciprocalSquarePairSlope t x)
      (Ioi (t + H)) := by
  have hl : IntegrableOn (fun x => (Real.log x - c) * reciprocalSquarePair t x)
      (Ioi (t + H)) := by
    rw [add_comm t H, ← integrableOn_Ioi_comp_add_iff t H]
    exact integrableOn_log_sub_reciprocalSquarePair_add ht hH c
  apply (hl.abs.const_mul (2 / H)).mono'
    (by apply Measurable.aestronglyMeasurable; unfold reciprocalSquarePairSlope; fun_prop)
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  have hx' : t < x := by have : t + H < x := hx; linarith
  rw [Real.norm_eq_abs, abs_mul,
    abs_of_nonneg (reciprocalSquarePairSlope_nonneg ht.le hx'),
    abs_mul, abs_of_pos (reciprocalSquarePair_pos ht.le hx')]
  calc
    _ ≤ |Real.log x - c| * ((2 / H) * reciprocalSquarePair t x) :=
      mul_le_mul_of_nonneg_left (reciprocalSquarePairSlope_le ht.le hH hx.le) (abs_nonneg _)
    _ = _ := by ring

/-- A further linear factor is permitted in the logarithmic derivative-weight integral. -/
theorem integrableOn_mul_log_sub_mul_reciprocalSquarePairSlope {t H : ℝ}
    (ht : 0 < t) (hH : 0 < H) (c : ℝ) :
    IntegrableOn (fun x => x * (Real.log x - c) * reciprocalSquarePairSlope t x)
      (Ioi (t + H)) := by
  have hl : IntegrableOn (fun x => (Real.log x - c) * reciprocalSquarePair t x)
      (Ioi (t + H)) := by
    rw [add_comm t H, ← integrableOn_Ioi_comp_add_iff t H]
    exact integrableOn_log_sub_reciprocalSquarePair_add ht hH c
  apply (hl.abs.const_mul (2 * (1 + t / H))).mono'
    (by apply Measurable.aestronglyMeasurable; unfold reciprocalSquarePairSlope; fun_prop)
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  have hx' : t < x := by have : t + H < x := hx; linarith
  have hx₀ : 0 < x := ht.trans hx'
  rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_pos hx₀,
    abs_of_nonneg (reciprocalSquarePairSlope_nonneg ht.le hx'),
    abs_mul, abs_of_pos (reciprocalSquarePair_pos ht.le hx')]
  calc
    _ = |Real.log x - c| * (x * reciprocalSquarePairSlope t x) := by ring
    _ ≤ |Real.log x - c| * (2 * (1 + t / H) * reciprocalSquarePair t x) :=
      mul_le_mul_of_nonneg_left (mul_reciprocalSquarePairSlope_le ht.le hH hx.le) (abs_nonneg _)
    _ = _ := by ring

/-- Dividing the pair by the height gives an integrable unshifted tail. -/
theorem integrableOn_reciprocalSquarePair_div {t H : ℝ} (ht : 0 < t) (hH : 0 < H) :
    IntegrableOn (fun x => reciprocalSquarePair t x / x) (Ioi (t + H)) := by
  rw [add_comm t H, ← integrableOn_Ioi_comp_add_iff t H]
  exact integrableOn_reciprocalSquarePair_div_add ht hH

/-- Exact integration by parts, retaining an arbitrary constant in the logarithmic weight. -/
theorem integral_log_sub_mul_reciprocalSquarePairSlope {t H : ℝ}
    (ht : 0 < t) (hH : 0 < H) (c : ℝ) :
    (∫ x in Ioi (t + H), (Real.log x - c) * reciprocalSquarePairSlope t x) =
      (Real.log (t + H) - c) * reciprocalSquarePair t (t + H) +
        ∫ x in Ioi (t + H), reciprocalSquarePair t x / x := by
  have hd (x : ℝ) (hx : x ∈ Ici (t + H)) :
      HasDerivAt (fun y => (Real.log y - c) * reciprocalSquarePair t y)
        (reciprocalSquarePair t x / x -
          (Real.log x - c) * reciprocalSquarePairSlope t x) x := by
    have hx' : t + H ≤ x := hx
    have hxpos : 0 < x := by linarith
    convert ((hasDerivAt_log hxpos.ne').sub_const c).mul
      (hasDerivAt_reciprocalSquarePair (by linarith : x - t ≠ 0)
        (by linarith : x + t ≠ 0)) using 1
    unfold reciprocalSquarePairSlope
    ring
  have hD := integrableOn_reciprocalSquarePair_div ht hH
  have hL := integrableOn_log_sub_mul_reciprocalSquarePairSlope ht hH c
  have hi : IntegrableOn (fun x => reciprocalSquarePair t x / x -
      (Real.log x - c) * reciprocalSquarePairSlope t x) (Ioi (t + H)) :=
    (hD.sub hL).congr_fun (fun _ _ => rfl) measurableSet_Ioi
  have hlim := tendsto_log_sub_mul_reciprocalSquarePair_atTop t c
  have h := integral_Ioi_of_hasDerivAt_of_tendsto' hd hi hlim
  rw [integral_sub hD hL] at h
  linarith

/-- The zero-offset specialization gives the logarithmic derivative-weight integral. -/
theorem integral_log_mul_reciprocalSquarePairSlope {t H : ℝ} (ht : 0 < t) (hH : 0 < H) :
    (∫ x in Ioi (t + H), Real.log x * reciprocalSquarePairSlope t x) =
      Real.log (t + H) * reciprocalSquarePair t (t + H) +
        ∫ x in Ioi (t + H), reciprocalSquarePair t x / x := by
  simpa only [sub_zero] using integral_log_sub_mul_reciprocalSquarePairSlope ht hH 0

end Real
