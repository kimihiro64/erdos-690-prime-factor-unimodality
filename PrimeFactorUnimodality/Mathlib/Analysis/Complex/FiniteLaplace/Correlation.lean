/-
Copyright (c) 2026 Jonas Whidden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonas Whidden
-/
import PrimeFactorUnimodality.Mathlib.Analysis.Complex.FiniteLaplace.Basic
import PrimeFactorUnimodality.Mathlib.Analysis.Complex.FiniteLaplace.VolterraEnergy
import PrimeFactorUnimodality.Mathlib.MeasureTheory.Integral.IntervalIntegral.Triangle

/-! # Positivity of the finite correlation transform

Triangular Fubini identifies the transform of an overlap correlation with
a Volterra quadratic form. Its exact energy identity proves nonnegativity
of the real part on the closed right half-plane, including the boundary.
The source may change sign; only continuity is needed.
-/

namespace Complex

noncomputable section

open MeasureTheory Set
open scoped Topology

/-- The overlap transform is exactly the backward Volterra quadratic form. -/
theorem finiteLaplace_correlation_eq_neg_volterra {q : ℝ → ℝ} (hq : Continuous q)
    {a b : ℝ} (hab : a ≤ b) (s : ℂ) :
    finiteLaplace (fun u => ((∫ v in a..b - u, q v * q (v + u) : ℝ) : ℂ)) (b - a) s =
      -(∫ v in a..b, (q v : ℂ) * finiteVolterra q b (-s) v) := by
  have hcast (u : ℝ) : ((∫ v in a..b - u, q v * q (v + u) : ℝ) : ℂ) =
      ∫ v in a..b - u, (q v : ℂ) * (q (v + u) : ℂ) := by
    rw [← intervalIntegral.integral_ofReal]
    simp only [ofReal_mul]
  unfold finiteLaplace
  simp_rw [hcast, ← intervalIntegral.integral_const_mul]
  rw [intervalIntegral.integral_integral_triangle_swap
    (F := fun p : ℝ × ℝ => exp (-s * (p.1 : ℂ)) * ((q p.2 : ℂ) * (q (p.2 + p.1) : ℂ)))
    (by fun_prop) hab, ← intervalIntegral.integral_neg]
  apply intervalIntegral.integral_congr
  intro v _
  have hphase (u : ℝ) : exp (-s * (u : ℂ)) =
      exp (s * (v : ℂ)) * exp (-s * ((v + u : ℝ) : ℂ)) := by
    rw [← exp_add]
    congr 1
    push_cast
    ring
  have hfactor (u : ℝ) :
      exp (-s * (u : ℂ)) *
        ((q v : ℂ) * (q (v + u) : ℂ)) =
      ((q v : ℂ) * exp (s * (v : ℂ))) *
        (exp (-s * ((v + u : ℝ) : ℂ)) * (q (v + u) : ℂ)) := by
    rw [hphase u]
    ring
  simp_rw [hfactor]
  rw [intervalIntegral.integral_const_mul,
    intervalIntegral.integral_comp_add_left (fun w : ℝ => exp (-s * (w : ℂ)) * (q w : ℂ)) v]
  simp only [add_zero, add_sub_cancel, finiteVolterra, neg_neg]
  rw [intervalIntegral.integral_symm b v]
  ring

/-- Exact energy representation for the real correlation transform. -/
theorem re_finiteLaplace_correlation_eq_energy {q : ℝ → ℝ} (hq : Continuous q)
    {a b : ℝ} (hab : a ≤ b) (s : ℂ) :
    (finiteLaplace (fun u => ((∫ v in a..b - u, q v * q (v + u) : ℝ) : ℂ)) (b - a) s).re =
      ‖finiteVolterra q b (-s) a‖ ^ 2 / 2 +
        s.re * ∫ v in a..b, ‖finiteVolterra q b (-s) v‖ ^ 2 := by
  rw [finiteLaplace_correlation_eq_neg_volterra hq hab]
  have hi : IntervalIntegrable (fun v => (q v : ℂ) * finiteVolterra q b (-s) v) volume a b :=
    ((continuous_ofReal.comp hq).mul (continuous_finiteVolterra hq b (-s))).intervalIntegrable a b
  have hre := reCLM.intervalIntegral_comp_comm hi
  simp only [reCLM_apply, mul_re, ofReal_re, ofReal_im, zero_mul, sub_zero] at hre
  rw [neg_re, ← hre]
  have he := integral_mul_re_finiteVolterra_eq hq b a (-s)
  rw [intervalIntegral.integral_symm a b, intervalIntegral.integral_symm a b, neg_re, neg_mul_neg]
    at he
  exact he

/-- The real Laplace transform of any continuous finite autocorrelation is nonnegative. -/
theorem re_finiteLaplace_correlation_nonneg {q : ℝ → ℝ} (hq : Continuous q)
    {a b : ℝ} (hab : a ≤ b) {s : ℂ} (hs : 0 ≤ s.re) :
    0 ≤ (finiteLaplace (fun u => ((∫ v in a..b - u, q v * q (v + u) : ℝ) : ℂ))
      (b - a) s).re := by
  rw [re_finiteLaplace_correlation_eq_energy hq hab]
  exact add_nonneg (by positivity) (mul_nonneg hs
    (intervalIntegral.integral_nonneg hab (fun _ _ => sq_nonneg _)))

/-- A nonzero source gives strict positivity in the open right half-plane. -/
theorem re_finiteLaplace_correlation_pos {q : ℝ → ℝ} (hq : Continuous q)
    {a b : ℝ} (hqn : ∃ c ∈ Ioo a b, q c ≠ 0) {s : ℂ} (hs : 0 < s.re) :
    0 < (finiteLaplace (fun u => ((∫ v in a..b - u, q v * q (v + u) : ℝ) : ℂ))
      (b - a) s).re := by
  obtain ⟨c, hc, hqc⟩ := hqn
  have hab : a < b := hc.1.trans hc.2
  have hQ := continuous_finiteVolterra hq b (-s)
  have hex : ∃ v ∈ Icc a b, finiteVolterra q b (-s) v ≠ 0 := by
    by_contra! hz
    have heq : finiteVolterra q b (-s) =ᶠ[𝓝 c] fun _ => (0 : ℂ) := by
      filter_upwards [isOpen_Ioo.mem_nhds hc] with v hv
      exact hz v ⟨hv.1.le, hv.2.le⟩
    have hzero : HasDerivAt (finiteVolterra q b (-s)) 0 c :=
      (hasDerivAt_const c (0 : ℂ)).congr_of_eventuallyEq heq
    have hd := (hasDerivAt_finiteVolterra hq b (-s) c).unique hzero
    rw [hz c ⟨hc.1.le, hc.2.le⟩, mul_zero, sub_zero, ofReal_eq_zero] at hd
    exact hqc hd
  have henergy : 0 < ∫ v in a..b, ‖finiteVolterra q b (-s) v‖ ^ 2 := by
    apply intervalIntegral.integral_pos hab (hQ.norm.pow 2).continuousOn
      (fun _ _ => sq_nonneg _)
    obtain ⟨v, hv, hne⟩ := hex
    exact ⟨v, hv, pow_pos (norm_pos_iff.mpr hne) 2⟩
  rw [re_finiteLaplace_correlation_eq_energy hq hab.le]
  exact add_pos_of_nonneg_of_pos (by positivity) (mul_pos hs henergy)

end

end Complex
