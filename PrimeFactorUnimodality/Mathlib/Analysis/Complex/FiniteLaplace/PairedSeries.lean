/-
Copyright (c) 2026 Jonas Whidden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonas Whidden
-/
import Mathlib.Analysis.Complex.LocallyUniformLimit
import PrimeFactorUnimodality.Mathlib.Analysis.Complex.FiniteLaplace.Differentiability
import PrimeFactorUnimodality.Mathlib.Analysis.Complex.FiniteLaplace.PairedBounds

/-! # Entire sums of paired finite Laplace contributions

For a locally finite inverse-square family in a left half-plane,
`sum_i (F(s-a_i)+f(0)/a_i)` is entire. A summable majorant is constructed
on every parameter ball: finitely many near terms use compactness, and
the remaining terms use the uniform inverse-square tail bound.
Repeated values in the family retain their multiplicities.
-/

namespace Complex

noncomputable section

open Set Filter

/-- An entire paired series has a summable majorant on each closed parameter ball. -/
theorem exists_summable_bound_finiteLaplace_add_reciprocal
    {ι : Type*} (a : ι → ℂ) (hfinite : ∀ R : ℝ, {i | ‖a i‖ ≤ R}.Finite)
    (hsum : Summable (fun i => ‖a i‖⁻¹ ^ 2)) {B : ℝ} (ha : ∀ i, (a i).re ≤ B)
    {f g h : ℝ → ℂ} {d M : ℝ} (hd : 0 ≤ d) (hM : 0 ≤ M)
    (hf : ContinuousOn f (Icc 0 d)) (hg : ContinuousOn g (Icc 0 d))
    (hh : ContinuousOn h (Icc 0 d))
    (hfg : ∀ t ∈ Ioo 0 d, HasDerivAt f (g t) t)
    (hgh : ∀ t ∈ Ioo 0 d, HasDerivAt g (h t) t)
    (hfd : f d = 0) (hg₀ : g 0 = 0) (hgd : g d = 0)
    (hbound : ∀ t ∈ Icc 0 d, ‖h t‖ ≤ M) (R : ℝ) :
    ∃ b : ι → ℝ, Summable b ∧ ∀ i s, ‖s‖ ≤ R →
      ‖finiteLaplace f d (s - a i) + f 0 / a i‖ ≤ b i := by
  classical
  have hf' : ContinuousOn f (uIcc 0 d) := by simpa only [uIcc_of_le hd] using hf
  have hc (i : ι) : Continuous (fun s : ℂ => finiteLaplace f d (s - a i) + f 0 / a i) := by
    have hcomp := (differentiable_finiteLaplace hf').continuous.comp
      (continuous_id.sub (continuous_const : Continuous (fun _ : ℂ => a i)))
    exact hcomp.add continuous_const
  choose b hb using fun i =>
    (isCompact_closedBall (0 : ℂ) R).exists_bound_of_continuousOn (hc i).continuousOn
  let C := 4 * M * d * Real.exp (max 0 (B + R) * d) + 2 * ‖f 0‖ * R
  let bound : ι → ℝ := fun i => if ‖a i‖ ≤ 2 * R then b i else C * ‖a i‖⁻¹ ^ 2
  have hsum' : Summable bound := (hsum.mul_left C).congr_cofinite (by
    filter_upwards [(hfinite (2 * R)).eventually_cofinite_notMem] with i hi
    simp [bound, hi])
  refine ⟨bound, hsum', ?_⟩
  intro i s hs
  dsimp only [bound]
  split_ifs with hi
  · exact hb i s (by simpa only [Metric.mem_closedBall, dist_zero_right] using hs)
  · exact norm_finiteLaplace_add_reciprocal_le_inv_sq hd hM hf hg hh hfg hgh
      hfd hg₀ hgd hbound hs (ha i) (lt_of_not_ge hi)

/-- The paired contributions are absolutely summable at every complex point. -/
theorem summable_finiteLaplace_add_reciprocal
    {ι : Type*} (a : ι → ℂ) (hfinite : ∀ R : ℝ, {i | ‖a i‖ ≤ R}.Finite)
    (hsum : Summable (fun i => ‖a i‖⁻¹ ^ 2)) {B : ℝ} (ha : ∀ i, (a i).re ≤ B)
    {f g h : ℝ → ℂ} {d M : ℝ} (hd : 0 ≤ d) (hM : 0 ≤ M)
    (hf : ContinuousOn f (Icc 0 d)) (hg : ContinuousOn g (Icc 0 d))
    (hh : ContinuousOn h (Icc 0 d))
    (hfg : ∀ t ∈ Ioo 0 d, HasDerivAt f (g t) t)
    (hgh : ∀ t ∈ Ioo 0 d, HasDerivAt g (h t) t)
    (hfd : f d = 0) (hg₀ : g 0 = 0) (hgd : g d = 0)
    (hbound : ∀ t ∈ Icc 0 d, ‖h t‖ ≤ M) (s : ℂ) :
    Summable (fun i => finiteLaplace f d (s - a i) + f 0 / a i) := by
  obtain ⟨b, hb, hbound'⟩ := exists_summable_bound_finiteLaplace_add_reciprocal
    a hfinite hsum ha hd hM hf hg hh hfg hgh hfd hg₀ hgd hbound ‖s‖
  exact hb.of_norm_bounded (fun i => hbound' i s le_rfl)

/-- Pairing with the reciprocal constant produces an entire zero sum. -/
theorem differentiable_tsum_finiteLaplace_add_reciprocal
    {ι : Type*} (a : ι → ℂ) (hfinite : ∀ R : ℝ, {i | ‖a i‖ ≤ R}.Finite)
    (hsum : Summable (fun i => ‖a i‖⁻¹ ^ 2)) {B : ℝ} (ha : ∀ i, (a i).re ≤ B)
    {f g h : ℝ → ℂ} {d M : ℝ} (hd : 0 ≤ d) (hM : 0 ≤ M)
    (hf : ContinuousOn f (Icc 0 d)) (hg : ContinuousOn g (Icc 0 d))
    (hh : ContinuousOn h (Icc 0 d))
    (hfg : ∀ t ∈ Ioo 0 d, HasDerivAt f (g t) t)
    (hgh : ∀ t ∈ Ioo 0 d, HasDerivAt g (h t) t)
    (hfd : f d = 0) (hg₀ : g 0 = 0) (hgd : g d = 0)
    (hbound : ∀ t ∈ Icc 0 d, ‖h t‖ ≤ M) :
    Differentiable ℂ (fun s => ∑' i, (finiteLaplace f d (s - a i) + f 0 / a i)) := by
  have hf' : ContinuousOn f (uIcc 0 d) := by simpa only [uIcc_of_le hd] using hf
  intro s
  obtain ⟨b, hb, hbound'⟩ := exists_summable_bound_finiteLaplace_add_reciprocal
    a hfinite hsum ha hd hM hf hg hh hfg hgh hfd hg₀ hgd hbound (‖s‖ + 1)
  have hdiff (i : ι) : Differentiable ℂ
      (fun w => finiteLaplace f d (w - a i) + f 0 / a i) := by
    have hcomp := (differentiable_finiteLaplace hf').comp (differentiable_id.sub_const (a i))
    exact hcomp.add_const (f 0 / a i)
  have h := differentiableOn_tsum_of_summable_norm hb
    (fun i => (hdiff i).differentiableOn) (U := Metric.ball 0 (‖s‖ + 1)) Metric.isOpen_ball
    (fun i w hw => hbound' i w (by
      exact (show ‖w‖ < ‖s‖ + 1 by simpa using hw).le))
  exact h.differentiableAt (Metric.isOpen_ball.mem_nhds (by
    simpa only [Metric.mem_ball, dist_zero_right] using lt_add_one ‖s‖))

end

end Complex
