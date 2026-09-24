/-
Copyright (c) 2026 Jonas Whidden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonas Whidden
-/
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-! # Absolute integrals and two-sided tails of exponential envelopes

The same finite exponential majorants used for lattice aliases also give
absolute integrability and explicit off-cell Fourier integrals.
-/

open MeasureTheory Set

namespace Fourier

/-- A two-sided decaying exponential is integrable on the whole real line. -/
theorem integrable_exp_neg_mul_abs {a : ℝ} (ha : 0 < a) :
    Integrable (fun x : ℝ => Real.exp (-a * |x|)) := by
  have hl : IntegrableOn (fun x : ℝ => Real.exp (-a * |x|)) (Iic 0) := by
    apply (integrableOn_exp_mul_Iic ha 0).congr_fun _ measurableSet_Iic
    intro x hx
    dsimp only
    rw [abs_of_nonpos hx]
    congr 1
    ring
  have hr : IntegrableOn (fun x : ℝ => Real.exp (-a * |x|)) (Ioi 0) := by
    apply (integrableOn_exp_mul_Ioi (neg_neg_of_pos ha) 0).congr_fun _ measurableSet_Ioi
    intro x hx
    dsimp only
    rw [abs_of_pos hx]
  simpa only [Iic_union_Ioi, integrableOn_univ] using hl.union hr

/-- The exact two-sided integral beyond a nonnegative cutoff. -/
theorem integral_exp_neg_mul_abs_compl {a R : ℝ} (ha : 0 < a) (hR : 0 ≤ R) :
    (∫ x in (Ioc (-R) R)ᶜ, Real.exp (-a * |x|)) =
      2 * (Real.exp (-a * R) / a) := by
  have hi := integrable_exp_neg_mul_abs ha
  have he : (Ioc (-R) R)ᶜ = Iic (-R) ∪ Ioi R := by
    ext x
    simp only [mem_compl_iff, mem_Ioc, mem_union, mem_Iic, mem_Ioi, not_and_or, not_lt, not_le]
  rw [he, setIntegral_union (by
      apply Set.disjoint_left.mpr
      intro x hx hy
      have : x ≤ -R := hx
      have : R < x := hy
      linarith) measurableSet_Ioi hi.integrableOn hi.integrableOn]
  have hl : (∫ x in Iic (-R), Real.exp (-a * |x|)) = Real.exp (-a * R) / a := by
    rw [setIntegral_congr_fun measurableSet_Iic (g := fun x => Real.exp (a * x)) (by
      intro x hx
      dsimp only
      rw [abs_of_nonpos (by have : x ≤ -R := hx; linarith)]
      congr 1
      ring), integral_exp_mul_Iic ha]
    congr 2
    ring
  have hr : (∫ x in Ioi R, Real.exp (-a * |x|)) = Real.exp (-a * R) / a := by
    rw [setIntegral_congr_fun measurableSet_Ioi (g := fun x => Real.exp (-a * x)) (by
      intro x hx
      dsimp only
      rw [abs_of_pos (lt_of_le_of_lt hR hx)]), integral_exp_mul_Ioi (neg_neg_of_pos ha)]
    ring
  rw [hl, hr, two_mul]

/-- Finite exponential majorants give integrability of a measurable vector-valued function. -/
theorem integrable_of_finite_exp_bound {ι E : Type*} [NormedAddCommGroup E]
    {s : Finset ι} {c a : ι → ℝ} {f : ℝ → E}
    (ha : ∀ i ∈ s, 0 < a i) (hm : AEStronglyMeasurable f)
    (hf : ∀ x, ‖f x‖ ≤ ∑ i ∈ s, c i * Real.exp (-a i * |x|)) : Integrable f := by
  have hi : Integrable (fun x : ℝ => ∑ i ∈ s, c i * Real.exp (-a i * |x|)) :=
    integrable_finsetSum s (fun i hi => (integrable_exp_neg_mul_abs (ha i hi)).const_mul (c i))
  exact hi.mono' hm (Filter.Eventually.of_forall hf)

/-- The actual norm tail is bounded by the exactly integrated finite exponential envelope. -/
theorem integral_norm_compl_le_of_finite_exp_bound {ι E : Type*} [NormedAddCommGroup E]
    {s : Finset ι} {c a : ι → ℝ} {f : ℝ → E} {R : ℝ}
    (ha : ∀ i ∈ s, 0 < a i) (hm : AEStronglyMeasurable f) (hR : 0 ≤ R)
    (hf : ∀ x, ‖f x‖ ≤ ∑ i ∈ s, c i * Real.exp (-a i * |x|)) :
    (∫ x in (Ioc (-R) R)ᶜ, ‖f x‖) ≤
      2 * ∑ i ∈ s, c i * (Real.exp (-a i * R) / a i) := by
  have hi (i : ι) (hi : i ∈ s) := (integrable_exp_neg_mul_abs (ha i hi)).const_mul (c i)
  have hb := integral_mono_ae (μ := volume.restrict (Ioc (-R) R)ᶜ)
    (integrable_of_finite_exp_bound ha hm hf).norm.integrableOn
    (integrable_finsetSum s hi).integrableOn (Filter.Eventually.of_forall hf)
  refine hb.trans_eq ?_
  rw [integral_finsetSum _ (fun i h => (hi i h).integrableOn), Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i h
  rw [integral_const_mul, integral_exp_neg_mul_abs_compl (ha i h) hR]
  ring

end Fourier
