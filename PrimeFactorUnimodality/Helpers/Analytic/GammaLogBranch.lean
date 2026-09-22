/-
Copyright (c) 2026 Robby Sneiderman. All rights reserved.
Copyright (c) 2026 Jonas Whidden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robby Sneiderman, Jonas Whidden
-/
import Mathlib.Analysis.Calculus.UniformLimitsDeriv
import Mathlib.Analysis.Normed.Group.FunctionSeries
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
import PrimeNumberTheoremAnd.Mathlib.Analysis.SpecialFunctions.Gamma.DigammaSeries

/-! # The canonical analytic logarithm of Gamma on the right half-plane

Use PNT's existing `Complex.logGammaSeq` and its proved convergence. Export
the derivative of its limit, which is local inside the proof of
`Complex.hasSum_digamma_of_re_pos` in Robby Sneiderman's Apache-2.0
`DigammaSeries.lean`, revision `f6147e7572ab3abe5428101bc0b13627bcb005df`.
The uniform-derivative argument below adapts that portion only, reusing the
proved packet majorant, summability, and digamma identity. This fixes the
logarithm branch needed for contour integration without assuming a phase.
-/

namespace PrimeFactorUnimodality

noncomputable section

open Complex Filter Set
open scoped Topology

/-- The limit of the Euler logarithmic Gamma approximants. -/
def gammaRightLog (z : ℂ) : ℂ := limUnder atTop (logGammaSeq z)

/-- Convergence to the chosen logarithm follows from the dependency's Cauchy theorem. -/
theorem tendsto_logGammaSeq {z : ℂ} (hz : 0 < z.re) :
    Tendsto (logGammaSeq z) atTop (𝓝 (gammaRightLog z)) :=
  (cauchySeq_logGammaSeq hz).tendsto_limUnder

/-- The finite approximant has the expected logarithmic derivative. -/
theorem hasDerivAt_logGammaSeq {z : ℂ} (hz : 0 < z.re) (n : ℕ) :
    HasDerivAt (fun w => logGammaSeq w n)
      ((Real.log n : ℂ) - ∑ m ∈ Finset.range (n + 1), (z + m)⁻¹) z := by
  have h1 : HasDerivAt (fun w : ℂ => w * (Real.log n : ℂ) + (Real.log n.factorial : ℂ))
      (Real.log n : ℂ) z := (hasDerivAt_mul_const _).add_const _
  have h2 : HasDerivAt (fun w : ℂ => ∑ m ∈ Finset.range (n + 1), log (w + m))
      (∑ m ∈ Finset.range (n + 1), (z + m)⁻¹) z := by
    apply HasDerivAt.fun_sum
    intro m _
    have hm : z + (m : ℂ) ∈ slitPlane := by
      apply Or.inl
      simp only [add_re, natCast_re]
      positivity
    simpa using! (hasDerivAt_log hm).comp z ((hasDerivAt_id z).add_const (m : ℂ))
  simpa only [logGammaSeq] using! h1.sub h2

/-- The chosen Gamma logarithm is an actual primitive of digamma. -/
theorem hasDerivAt_gammaRightLog {z : ℂ} (hz : 0 < z.re) :
    HasDerivAt gammaRightLog (digamma z) z := by
  let a := min (z.re / 2) 1
  let R := ‖z‖ + 1
  let s : Set ℂ := {w | a < w.re} ∩ {w | ‖w‖ < R}
  have ha : 0 < a := lt_min (by linarith) one_pos
  have ha1 : a ≤ 1 := min_le_right _ _
  have haz : a < z.re := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have hsz : z ∈ s := ⟨haz, by dsimp [R]; linarith⟩
  have hs : IsOpen s :=
    (isOpen_lt continuous_const continuous_re).inter (isOpen_lt continuous_norm continuous_const)
  have hp (w : ℂ) (hw : w ∈ s) : 0 < w.re := ha.trans hw.1
  have hu : Summable (fun m : ℕ => (R + 1) / (a * ((m : ℝ) + 1) ^ 2)) := by
    refine (summable_one_div_natCast_add_one_sq.mul_left ((R + 1) / a)).congr fun m => ?_
    rw [mul_one_div, div_div]
  have hM : TendstoUniformlyOn
      (fun (N : ℕ) (w : ℂ) => ∑ m ∈ Finset.range N, (((m : ℂ) + 1)⁻¹ - (w + m)⁻¹))
      (fun w : ℂ => ∑' m : ℕ, (((m : ℂ) + 1)⁻¹ - (w + m)⁻¹)) atTop s :=
    tendstoUniformlyOn_tsum_nat hu fun m w hw =>
      norm_inv_add_one_sub_inv_le ha ha1 hw.1.le hw.2.le m
  have hM1 : TendstoUniformlyOn
      (fun (n : ℕ) (w : ℂ) => ∑ m ∈ Finset.range (n + 1),
        (((m : ℂ) + 1)⁻¹ - (w + m)⁻¹))
      (fun w : ℂ => ∑' m : ℕ, (((m : ℂ) + 1)⁻¹ - (w + m)⁻¹)) atTop s := by
    intro u hu'
    exact (tendsto_add_atTop_nat 1).eventually (hM u hu')
  have hcR : Tendsto (fun n : ℕ => Real.log n - (harmonic n : ℝ) - ((n : ℝ) + 1)⁻¹)
      atTop (𝓝 (-Real.eulerMascheroniConstant)) := by
    have h1 : Tendsto (fun n : ℕ => Real.log n - (harmonic n : ℝ)) atTop
        (𝓝 (-Real.eulerMascheroniConstant)) :=
      Real.tendsto_harmonic_sub_log.neg.congr fun n => by ring
    have h2 : Tendsto (fun n : ℕ => ((n : ℝ) + 1)⁻¹) atTop (𝓝 0) :=
      Filter.Tendsto.inv_tendsto_atTop
        (tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop)
    simpa using h1.sub h2
  have hcC : Tendsto (fun n : ℕ =>
      ((Real.log n - (harmonic n : ℝ) - ((n : ℝ) + 1)⁻¹ : ℝ) : ℂ))
      atTop (𝓝 (-(Real.eulerMascheroniConstant : ℂ))) := by
    simpa only [ofReal_neg] using hcR.ofReal
  have hd : TendstoUniformlyOn
      (fun (n : ℕ) (w : ℂ) => (Real.log n : ℂ) - ∑ m ∈ Finset.range (n + 1), (w + m)⁻¹)
      (fun w : ℂ => -(Real.eulerMascheroniConstant : ℂ) +
        ∑' m : ℕ, (((m : ℂ) + 1)⁻¹ - (w + m)⁻¹)) atTop s := by
    refine ((hcC.tendstoUniformlyOn_const s).add hM1).congr ?_
    filter_upwards with n
    intro w _
    simp only [Pi.add_apply]
    rw [Finset.sum_sub_distrib, sum_inv_natCast_add_one (n + 1)]
    push_cast [harmonic_succ]
    ring
  have hk := hasDerivAt_of_tendstoUniformlyOn hs hd
    (Filter.Eventually.of_forall fun n w hw => hasDerivAt_logGammaSeq (hp w hw) n)
    (fun w hw => tendsto_logGammaSeq (hp w hw)) hsz
  rw [(hasSum_digamma_of_re_pos hz).tsum_eq] at hk
  convert hk using 1
  ring

/-- Exponentiating the canonical logarithm recovers Gamma. -/
theorem exp_gammaRightLog {z : ℂ} (hz : 0 < z.re) :
    exp (gammaRightLog z) = Gamma z := by
  have hl := continuous_exp.continuousAt.tendsto.comp (tendsto_logGammaSeq hz)
  have hg : Tendsto (GammaSeq z) atTop (𝓝 (exp (gammaRightLog z))) := by
    apply hl.congr'
    filter_upwards [eventually_ne_atTop 0] with n hn
    exact exp_logGammaSeq hz hn
  exact tendsto_nhds_unique hg (GammaSeq_tendsto_Gamma z)

/-- Positive real inputs select the real Gamma logarithm, with no winding offset. -/
theorem gammaRightLog_ofReal_im {x : ℝ} (hx : 0 < x) :
    (gammaRightLog (x : ℂ)).im = 0 := by
  have h : ∀ n, (logGammaSeq (x : ℂ) n).im = 0 := by
    intro n
    simp only [logGammaSeq, sub_im, add_im, mul_im, ofReal_im, mul_zero, zero_mul,
      add_zero, zero_sub]
    apply neg_eq_zero.mpr
    rw [im_sum]
    apply Finset.sum_eq_zero
    intro m _
    have hm : 0 < x + (m : ℝ) := by positivity
    rw [← ofReal_natCast, ← ofReal_add, ← ofReal_log hm.le]
    exact ofReal_im _
  have hl := continuous_im.continuousAt.tendsto.comp
    (tendsto_logGammaSeq (z := (x : ℂ)) hx)
  exact tendsto_nhds_unique hl (tendsto_nhds_of_eventually_eq
    (Filter.Eventually.of_forall h))

end

end PrimeFactorUnimodality
