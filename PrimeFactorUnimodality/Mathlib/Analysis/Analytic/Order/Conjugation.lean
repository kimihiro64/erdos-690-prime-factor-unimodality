/-
Copyright (c) 2026 Jonas Whidden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonas Whidden
-/
import Mathlib.Analysis.Analytic.Order
import Mathlib.Analysis.Calculus.Deriv.Star
import Mathlib.Analysis.Complex.CauchyIntegral

/-! # Analytic order under complex conjugation

Double conjugation preserves analyticity and the order of vanishing,
including infinite order. The local factorization proof is adapted from
`Kadiri.analyticAt_conj_conj` and `Kadiri.analyticOrderAt_conj_conj` in
`IEANTN/KadiriZeroCounting.lean`, Apache-2.0 repository
`kimihiro64/PrimeNumberTheoremAnd`, revision
`f6147e7572ab3abe5428101bc0b13627bcb005df` (Lean 4.33.1).
Only the two general lemmas are extracted; their derivative helper is
replaced by Mathlib's conjugation API. No zero-counting module is imported.
The same three public results are in
`BombieriVinogradov.ComplexAnalysis.AnalyticAt.{conj_conj,
analyticOrderAt_conj_conj,analyticOrderNatAt_conj_conj}`,
`Helpers/ComplexAnalysis/AnalyticOrderConjugation.lean`, Apache-2.0 revision
`7a1748306e026825ed6a5555516cc2f28989b2ac`. This candidate preserves those
statements in the upstream `Complex` namespace and uses only Mathlib imports.
-/

namespace Complex

open Filter
open scoped Topology ComplexConjugate

/-- Conjugating both source and target transports local complex analyticity. -/
theorem analyticAt_conj_conj {f : ℂ → ℂ} {z : ℂ} (hf : AnalyticAt ℂ f (conj z)) :
    AnalyticAt ℂ (fun w => conj (f (conj w))) z := by
  rw [analyticAt_iff_eventually_differentiableAt] at hf ⊢
  filter_upwards [(continuous_conj.tendsto z).eventually hf] with w hw
  exact differentiableAt_conj_conj_iff.mpr hw

/-- Double conjugation preserves the full analytic order, including the locally zero case. -/
theorem analyticOrderAt_conj_conj {f : ℂ → ℂ} {z : ℂ} (hf : AnalyticAt ℂ f (conj z)) :
    analyticOrderAt (fun w => conj (f (conj w))) z = analyticOrderAt f (conj z) := by
  have hcfc := analyticAt_conj_conj hf
  have hc := continuous_conj.tendsto z
  cases h : analyticOrderAt f (conj z) with
  | top =>
      rw [analyticOrderAt_eq_top] at h ⊢
      filter_upwards [hc.eventually h] with w hw
      rw [hw, map_zero]
  | coe n =>
      rw [hf.analyticOrderAt_eq_natCast] at h
      obtain ⟨g, hg, hg₀, hfg⟩ := h
      rw [hcfc.analyticOrderAt_eq_natCast]
      refine ⟨fun w => conj (g (conj w)), analyticAt_conj_conj hg, ?_, ?_⟩
      · simpa only [map_ne_zero] using hg₀
      · filter_upwards [hc.eventually hfg] with w hw
        rw [hw]
        simp only [smul_eq_mul, map_mul, map_pow, map_sub, conj_conj]

/-- The natural-valued multiplicity is likewise invariant under double conjugation. -/
theorem analyticOrderNatAt_conj_conj {f : ℂ → ℂ} {z : ℂ}
    (hf : AnalyticAt ℂ f (conj z)) :
    analyticOrderNatAt (fun w => conj (f (conj w))) z = analyticOrderNatAt f (conj z) :=
  congrArg ENat.toNat (analyticOrderAt_conj_conj hf)

end Complex
