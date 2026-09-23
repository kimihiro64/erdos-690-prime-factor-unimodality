import PrimeFactorUnimodality.Helpers.Analytic.TuringPoleContour
import PrimeFactorUnimodality.Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import PrimeFactorUnimodality.Mathlib.Analysis.SpecialFunctions.Complex.LogNormDeriv

/-! # Differentiating the finite horizontal log-modulus segment

A regular positive height has a compact rectangular neighborhood with no
zeta zeros or pole on the segment. The branch-independent log-modulus
derivative and compact dominated differentiation give the exact negative
horizontal argument integral. No zero-free rectangle is assumed as an
additional input: compactness constructs it from regularity of the height.
-/

namespace PrimeFactorUnimodality

noncomputable section

open Complex Filter MeasureTheory Set
open scoped Topology

/-- Regularity at one height supplies a uniformly nonvanishing compact rectangle. -/
theorem exists_turing_regular_rectangle {σ T : ℝ} (hT : 0 < T)
    (htop : ∀ z : ℂ, z.im = T → riemannXi z ≠ 0) :
    ∃ r : ℝ, 0 < r ∧ ∀ u ∈ Icc (T - r) (T + r),
      0 < u ∧ ∀ x ∈ Icc (1 / 2 : ℝ) σ, riemannZeta ((x : ℂ) + u * I) ≠ 0 := by
  have he : ∀ᶠ u : ℝ in 𝓝 T, ∀ x ∈ Icc (1 / 2 : ℝ) σ,
      riemannZeta ((x : ℂ) + u * I) ≠ 0 := by
    apply isCompact_Icc.eventually_forall_of_forall_eventually
    intro x _
    have h1 : (x : ℂ) + T * I ≠ 1 := by
      intro hx
      exact hT.ne' (by simpa using congrArg Complex.im hx)
    have hz : riemannZeta ((x : ℂ) + T * I) ≠ 0 := fun hz =>
      htop _ (by simp) (riemannXi_eq_zero_of_zeta_zero_of_im_ne_zero (by simpa using hT.ne') hz)
    have hc : ContinuousAt (fun p : ℝ × ℝ => riemannZeta ((p.2 : ℂ) + p.1 * I)) (T, x) :=
      (differentiableAt_riemannZeta h1).continuousAt.comp
        (f := fun p : ℝ × ℝ => (p.2 : ℂ) + p.1 * I) (by fun_prop)
    exact hc.eventually_ne hz
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.mp (he.and (eventually_gt_nhds hT))
  refine ⟨δ / 2, by positivity, ?_⟩
  intro u hu
  have hb : u ∈ Metric.ball T δ := by
    rw [Metric.mem_ball, Real.dist_eq, abs_lt]
    constructor <;> linarith [hu.1, hu.2]
  exact ⟨(hball hb).2, (hball hb).1⟩

/-- At a nonzero zeta value, the height derivative has the Cauchy--Riemann sign. -/
theorem hasDerivAt_turingHorizontalLog {x T : ℝ} (hT : T ≠ 0)
    (hz : riemannZeta ((x : ℂ) + T * I) ≠ 0) :
    HasDerivAt (fun t : ℝ => Real.log ‖riemannZeta ((x : ℂ) + t * I)‖)
      (-(logDeriv riemannZeta ((x : ℂ) + T * I)).im) T := by
  have h1 : (x : ℂ) + T * I ≠ 1 := by
    intro he
    exact hT (by simpa using congrArg Complex.im he)
  exact (differentiableAt_riemannZeta h1).hasDerivAt.log_norm_vertical hz

/-- The finite log-modulus integral differentiates exactly at every regular positive height. -/
theorem hasDerivAt_turingHorizontalLog_finite {σ T : ℝ} (hσ : (1 / 2 : ℝ) ≤ σ)
    (hT : 0 < T) (htop : ∀ z : ℂ, z.im = T → riemannXi z ≠ 0) :
    HasDerivAt (fun t : ℝ => ∫ x in (1 / 2 : ℝ)..σ,
      Real.log ‖riemannZeta ((x : ℂ) + t * I)‖)
      (-(HIntegral (logDeriv riemannZeta) (1 / 2) σ T).im) T := by
  obtain ⟨r, hr, hrect⟩ := exists_turing_regular_rectangle (σ := σ) hT htop
  have h1 {p : ℝ × ℝ} (hp : p ∈ Icc (T - r) (T + r) ×ˢ uIcc (1 / 2 : ℝ) σ) :
      (p.2 : ℂ) + p.1 * I ≠ 1 := by
    intro he
    exact (hrect p.1 hp.1).1.ne' (by simpa using congrArg Complex.im he)
  have hz {p : ℝ × ℝ} (hp : p ∈ Icc (T - r) (T + r) ×ˢ uIcc (1 / 2 : ℝ) σ) :
      riemannZeta ((p.2 : ℂ) + p.1 * I) ≠ 0 :=
    (hrect p.1 hp.1).2 p.2 (uIcc_of_le hσ ▸ hp.2)
  have hc {p : ℝ × ℝ} (hp : p ∈ Icc (T - r) (T + r) ×ˢ uIcc (1 / 2 : ℝ) σ) :
      ContinuousAt (fun q : ℝ × ℝ => riemannZeta ((q.2 : ℂ) + q.1 * I)) p :=
    (differentiableAt_riemannZeta (h1 hp)).continuousAt.comp
      (f := fun q : ℝ × ℝ => (q.2 : ℂ) + q.1 * I) (by fun_prop)
  have hd := intervalIntegral.hasDerivAt_integral_of_continuousOn_rectangle
    (F := fun t x => Real.log ‖riemannZeta ((x : ℂ) + t * I)‖)
    (F' := fun t x => -(logDeriv riemannZeta ((x : ℂ) + t * I)).im) hr
    (fun p hp => ((hc hp).norm.log (norm_ne_zero_iff.mpr (hz hp))).continuousWithinAt)
    (by
      intro p hp
      have hdc : ContinuousAt (fun q : ℝ × ℝ => deriv riemannZeta ((q.2 : ℂ) + q.1 * I)) p :=
        (analyticOn_riemannZeta _ (h1 hp)).deriv.continuousAt.comp
          (f := fun q : ℝ × ℝ => (q.2 : ℂ) + q.1 * I) (by fun_prop)
      exact ((continuous_im.continuousAt.comp (hdc.div (hc hp) (hz hp))).neg).continuousWithinAt)
    (by
      intro u hu x hx
      exact hasDerivAt_turingHorizontalLog (hrect u ⟨hu.1.le, hu.2.le⟩).1.ne'
        ((hrect u ⟨hu.1.le, hu.2.le⟩).2 x (uIcc_of_le hσ ▸ hx)))
  have hi := intervalIntegrable_turingZetaLogDeriv hσ hT htop
  have him : (∫ x in (1 / 2 : ℝ)..σ, (logDeriv riemannZeta ((x : ℂ) + T * I)).im) =
      (HIntegral (logDeriv riemannZeta) (1 / 2) σ T).im :=
    intervalIntegral.intervalIntegral_im hi
  rwa [intervalIntegral.integral_neg, him] at hd

end

end PrimeFactorUnimodality
