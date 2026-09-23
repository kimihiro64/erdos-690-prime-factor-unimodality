/-
Copyright (c) 2026 Jonas Whidden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonas Whidden
-/
import Mathlib.Analysis.Meromorphic.FactorizedRational
import PrimeFactorUnimodality.Mathlib.Analysis.Complex.Log.HorizontalContinuity

/-! # Finite factorization of horizontal logarithmic integrals

On a compact set, Mathlib's meromorphic factorization leaves finitely many
exceptional points. Their real projections are null on every horizontal
line. Consequently the logarithmic integral is a finite sum of logarithmic
distances and an integral of a continuous remainder, even on lines through
zeros or poles. No enumeration or numerical bound on the zeros is needed.
-/

namespace MeromorphicOn

noncomputable section

open Complex Filter MeasureTheory Set

/-- A compact meromorphic factorization splits every contained horizontal logarithmic integral. -/
theorem exists_horizontal_log_integral_factorization {f : ℂ → ℂ} {K : Set ℂ}
    (hf : MeromorphicOn f K) (hK : IsCompact K)
    (horder : ∀ z : K, meromorphicOrderAt f z ≠ ⊤) :
    ∃ (s : Finset ℂ) (n : ℂ → ℤ) (g : ℂ → ℝ), ContinuousOn g K ∧
      ∀ a b t : ℝ, (∀ x ∈ uIcc a b, (x : ℂ) + t * I ∈ K) →
        (∫ x in a..b, Real.log ‖f ((x : ℂ) + t * I)‖) =
          (∑ w ∈ s, (n w : ℝ) * ∫ x in a..b, Real.log ‖(x : ℂ) + t * I - w‖) +
            ∫ x in a..b, g ((x : ℂ) + t * I) := by
  classical
  let D := divisor f K
  have hD : D.support.Finite := D.finiteSupport hK
  obtain ⟨g, hg, hgn, he⟩ := hf.extract_zeros_poles horder hD
  have hlog := extract_zeros_poles_log hgn he
  let s := hD.toFinset
  have hsum : (∑ᶠ w, fun z : ℂ => (D w : ℝ) * Real.log ‖z - w‖) =
      (fun z : ℂ => ∑ w ∈ s, (D w : ℝ) * Real.log ‖z - w‖) := by
    rw [finsum_eq_sum_of_support_subset (s := s) _ (by
      intro w hw
      by_contra hn
      have hz : D w = 0 := by simpa [s, Function.mem_support] using hn
      apply hw
      funext z
      simp [hz])]
    funext z
    simp only [Finset.sum_apply]
  have he' : (fun z => Real.log ‖f z‖) =ᶠ[codiscreteWithin K]
      (fun z => (∑ w ∈ s, (D w : ℝ) * Real.log ‖z - w‖) + Real.log ‖g z‖) := by
    change (fun z => Real.log ‖f z‖) =ᶠ[codiscreteWithin K]
      ((∑ᶠ w, fun z : ℂ => (D w : ℝ) * Real.log ‖z - w‖) +
        fun z => Real.log ‖g z‖) at hlog
    rw [hsum] at hlog
    exact hlog
  have hbad := hK.finite_sdiff_of_mem_codiscreteWithin he'
  have hc : ContinuousOn (fun z => Real.log ‖g z‖) K :=
    hg.continuousOn.norm.log (fun z hz => norm_ne_zero_iff.mpr (hgn ⟨z, hz⟩))
  refine ⟨s, D, (fun z => Real.log ‖g z‖), hc, ?_⟩
  intro a b t hline
  have hgi : IntervalIntegrable (fun x : ℝ => Real.log ‖g ((x : ℂ) + t * I)‖)
      volume a b :=
    (hc.comp (by fun_prop : ContinuousOn (fun x : ℝ => (x : ℂ) + t * I) (uIcc a b))
      hline).intervalIntegrable
  have hwi (w : ℂ) : IntervalIntegrable
      (fun x : ℝ => (D w : ℝ) * Real.log ‖(x : ℂ) + t * I - w‖) volume a b :=
    (intervalIntegrable_log_norm_horizontal_sub w t a b).const_mul _
  have hsi : IntervalIntegrable
      (fun x : ℝ => ∑ w ∈ s, (D w : ℝ) * Real.log ‖(x : ℂ) + t * I - w‖) volume a b := by
    convert IntervalIntegrable.sum s (fun w _ => hwi w) using 1
    funext x
    simp only [Finset.sum_apply]
  calc
    _ = ∫ x in a..b, (∑ w ∈ s, (D w : ℝ) * Real.log ‖(x : ℂ) + t * I - w‖) +
        Real.log ‖g ((x : ℂ) + t * I)‖ := by
      apply intervalIntegral.integral_congr_ae
      filter_upwards [(hbad.image Complex.re).countable.ae_notMem volume] with x hx hxab
      by_contra hn
      apply hx
      exact ⟨(x : ℂ) + t * I, ⟨hline x (uIoc_subset_uIcc hxab), hn⟩, by simp⟩
    _ = _ := by
      rw [intervalIntegral.integral_add hsi hgi,
        intervalIntegral.integral_finsetSum (fun w _ => hwi w)]
      simp only [intervalIntegral.integral_const_mul]

end

end MeromorphicOn
