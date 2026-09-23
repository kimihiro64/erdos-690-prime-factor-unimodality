/-
Copyright (c) 2026 Jonas Whidden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonas Whidden
-/
import Mathlib.NumberTheory.LSeries.Nonvanishing
import PrimeFactorUnimodality.Mathlib.Analysis.Meromorphic.HorizontalContinuity

/-! # Continuity of finite horizontal zeta logarithmic integrals

A compact rectangle at positive height avoids the pole at one. Widening
it to include real part two provides a nonzero value, so connectedness
excludes infinite analytic order everywhere. Finite meromorphic
factorization then proves continuity even at heights containing zeros.
-/

noncomputable section

open Complex Set
open scoped Topology

/-- Finite horizontal zeta log-modulus integrals are continuous at every positive height. -/
theorem continuousAt_integral_log_norm_riemannZeta_horizontal {T : ℝ} (hT : 0 < T)
    (a b : ℝ) :
    ContinuousAt (fun t : ℝ => ∫ x in a..b, Real.log ‖riemannZeta ((x : ℂ) + t * I)‖) T := by
  let lo := min (min a b) 2
  let hi := max (max a b) 2
  let U := Icc lo hi ×ˢ Icc (T / 2) (2 * T)
  let φ : ℝ × ℝ → ℂ := fun p => (p.1 : ℂ) + p.2 * I
  let K := φ '' U
  have hφ : Continuous φ := by fun_prop
  have hK : IsCompact K := (isCompact_Icc.prod isCompact_Icc).image hφ
  have hconn : IsPreconnected K :=
    (isPreconnected_Icc.prod isPreconnected_Icc).image φ hφ.continuousOn
  have h1 : ∀ z ∈ K, z ≠ 1 := by
    rintro z ⟨p, hp, rfl⟩ he
    have him : p.2 = 0 := by simpa [φ] using congrArg Complex.im he
    have hl := hp.2.1
    linarith
  have hf : MeromorphicOn riemannZeta K := fun z hz =>
    (analyticOn_riemannZeta z (h1 z hz)).meromorphicAt
  have hmem : (2 : ℂ) + T * I ∈ K := by
    refine ⟨(2, T), ⟨⟨min_le_right _ _, le_max_right _ _⟩, ?_⟩, rfl⟩
    constructor <;> linarith
  have ha := analyticOn_riemannZeta _ (h1 _ hmem)
  have hn : riemannZeta ((2 : ℂ) + T * I) ≠ 0 :=
    riemannZeta_ne_zero_of_one_lt_re (by simp)
  have ho : meromorphicOrderAt riemannZeta ((2 : ℂ) + T * I) ≠ ⊤ := by
    rw [ha.meromorphicOrderAt_eq, ha.analyticOrderAt_eq_zero.mpr hn]
    simp
  have hord : ∀ z : K, meromorphicOrderAt riemannZeta z ≠ ⊤ := fun z =>
    hf.meromorphicOrderAt_ne_top_of_isPreconnected hconn hmem z.2 ho
  have hc := hf.continuousOn_integral_log_norm_horizontal hK hord
    (a := a) (b := b) (c := T / 2) (d := 2 * T) (by linarith) (by
      intro t ht x hx
      refine ⟨(x, t), ⟨⟨?_, ?_⟩, ht⟩, rfl⟩
      · exact (min_le_left _ _).trans hx.1
      · exact hx.2.trans (le_max_left _ _))
  exact hc.continuousAt (Icc_mem_nhds (by linarith) (by linarith))

/-- The continuity includes all positive zero ordinates and either orientation of the segment. -/
theorem continuousOn_integral_log_norm_riemannZeta_horizontal (a b : ℝ) :
    ContinuousOn (fun t : ℝ => ∫ x in a..b, Real.log ‖riemannZeta ((x : ℂ) + t * I)‖)
      (Ioi 0) := fun _ ht =>
  (continuousAt_integral_log_norm_riemannZeta_horizontal ht a b).continuousWithinAt
