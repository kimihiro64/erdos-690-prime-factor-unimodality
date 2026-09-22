/-
Copyright (c) 2026 Jonas Whidden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonas Whidden
-/
import Mathlib.Analysis.SpecialFunctions.JapaneseBracket
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! # Logarithmically weighted Cauchy kernels

A shifted Cauchy kernel remains integrable after multiplication by a
logarithm. The proof gives a pointwise majorant by `(1 + |t|)^(-3/2)`;
the positive horizontal separation excludes singularities on the line.
-/

namespace Real

open MeasureTheory

/-- An explicit comparison between a shifted quadratic and the usual integrable weight. -/
theorem one_add_abs_sq_le_cauchy {a : ℝ} (ha : 0 < a) (b t : ℝ) :
    (1 + |t|) ^ 2 ≤ (4 + (2 + 4 * b ^ 2) / a ^ 2) * (a ^ 2 + (t - b) ^ 2) := by
  have ha₂ : 0 < a ^ 2 := sq_pos_of_pos ha
  have hbase : (1 + |t|) ^ 2 ≤ 2 + 4 * b ^ 2 + 4 * (t - b) ^ 2 := by
    nlinarith [sq_nonneg (|t| - 1), sq_abs t, sq_nonneg (t - 2 * b)]
  have hcancel : (2 + 4 * b ^ 2) / a ^ 2 * a ^ 2 = 2 + 4 * b ^ 2 :=
    div_mul_cancel₀ _ ha₂.ne'
  have hpos : 0 ≤ (2 + 4 * b ^ 2) / a ^ 2 * (t - b) ^ 2 := by positivity
  nlinarith [sq_nonneg a]

/-- A logarithmic Cauchy kernel is dominated by an explicit integrable power. -/
theorem log_add_abs_div_cauchy_le {a c : ℝ} (ha : 0 < a) (hc : 1 ≤ c) (b t : ℝ) :
    log (|t| + c) / (a ^ 2 + (t - b) ^ 2) ≤
      (2 * c ^ (1 / 2 : ℝ) * (4 + (2 + 4 * b ^ 2) / a ^ 2)) *
        (1 + |t|) ^ (-(3 / 2 : ℝ)) := by
  have hw : 0 < 1 + |t| := by positivity
  have hd : 0 < a ^ 2 + (t - b) ^ 2 := by positivity
  have hc₀ : 0 ≤ c := by linarith
  have harg : |t| + c ≤ c * (1 + |t|) := by
    nlinarith [abs_nonneg t]
  have hlog : log (|t| + c) ≤ 2 * c ^ (1 / 2 : ℝ) * (1 + |t|) ^ (1 / 2 : ℝ) := by
    calc
      _ ≤ (|t| + c) ^ (1 / 2 : ℝ) / (1 / 2 : ℝ) :=
        log_le_rpow_div (by positivity) (by norm_num)
      _ ≤ (c * (1 + |t|)) ^ (1 / 2 : ℝ) / (1 / 2 : ℝ) :=
        div_le_div_of_nonneg_right (rpow_le_rpow (by positivity) harg (by norm_num))
          (by norm_num)
      _ = _ := by rw [mul_rpow hc₀ hw.le]; ring
  have hquot : 1 / (a ^ 2 + (t - b) ^ 2) ≤
      (4 + (2 + 4 * b ^ 2) / a ^ 2) / (1 + |t|) ^ 2 := by
    apply (div_le_div_iff₀ hd (sq_pos_of_pos hw)).mpr
    simpa using one_add_abs_sq_le_cauchy ha b t
  have hpow : (1 + |t|) ^ (1 / 2 : ℝ) / (1 + |t|) ^ 2 =
      (1 + |t|) ^ (-(3 / 2 : ℝ)) := by
    rw [← rpow_natCast (1 + |t|) 2, ← rpow_sub hw]
    norm_num
  calc
    _ ≤ (2 * c ^ (1 / 2 : ℝ) * (1 + |t|) ^ (1 / 2 : ℝ)) *
        ((4 + (2 + 4 * b ^ 2) / a ^ 2) / (1 + |t|) ^ 2) := by
      rw [div_eq_mul_one_div]
      exact mul_le_mul hlog hquot (by positivity) (by positivity)
    _ = _ := by rw [← hpow]; ring

/-- Absolute integrability on the whole real line, for every positive separation. -/
theorem integrable_log_add_abs_div_cauchy {a c : ℝ} (ha : 0 < a) (hc : 1 ≤ c) (b : ℝ) :
    Integrable (fun t : ℝ => log (|t| + c) / (a ^ 2 + (t - b) ^ 2)) := by
  have hp : Integrable (fun t : ℝ => (1 + |t|) ^ (-(3 / 2 : ℝ))) := by
    simpa only [Real.norm_eq_abs] using
      (integrable_one_add_norm (E := ℝ) (μ := volume) (r := 3 / 2) (by norm_num))
  have hc₀ : 0 < c := lt_of_lt_of_le zero_lt_one hc
  refine (hp.const_mul (2 * c ^ (1 / 2 : ℝ) * (4 + (2 + 4 * b ^ 2) / a ^ 2))).mono'
    (Continuous.aestronglyMeasurable ?_) (.of_forall fun t => ?_)
  · have hlog : Continuous (fun t : ℝ => log (|t| + c)) :=
      (continuous_abs.add continuous_const).log
        (fun t => ne_of_gt (add_pos_of_nonneg_of_pos (abs_nonneg t) hc₀))
    exact hlog.div (by fun_prop) (fun t => ne_of_gt (by positivity))
  · rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg (log_nonneg (by
      linarith [abs_nonneg t])) (by positivity))]
    exact log_add_abs_div_cauchy_le ha hc b t

end Real
