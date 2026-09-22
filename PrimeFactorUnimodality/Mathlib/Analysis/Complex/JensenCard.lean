/-
Copyright (c) 2026 Jonas Whidden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonas Whidden
-/
import Mathlib.Analysis.Complex.JensenFormula

/-! # Distinct zeros and the divisor count in Jensen's inequality

On a compact connected analytic domain containing a nonzero value, every
zero contributes at least one to the nonnegative divisor. Distinct zeros
are therefore finite and their cardinality is bounded by the divisor sum.
This supplies the finite-zero interpretation of Mathlib's Jensen bound.
-/

open Complex MeromorphicOn Set

namespace AnalyticOnNhd

/-- A zero has positive divisor order if the analytic function is nontrivial on the domain. -/
theorem one_le_divisor_of_zero_of_isPreconnected {f : ℂ → ℂ} {U : Set ℂ} {c z : ℂ}
    (hf : AnalyticOnNhd ℂ f U) (hU : IsPreconnected U) (hc : c ∈ U) (hfc : f c ≠ 0)
    (hz : z ∈ U) (hfz : f z = 0) : 1 ≤ divisor f U z := by
  have htop : analyticOrderAt f z ≠ ⊤ := hf.analyticOrderAt_ne_top_of_isPreconnected
    hU hc hz (by rw [(hf c hc).analyticOrderAt_eq_zero.mpr hfc]; simp)
  have hn : analyticOrderNatAt f z ≠ 0 := by
    intro hn
    have ho : analyticOrderAt f z = 0 := by
      rw [← Nat.cast_analyticOrderNatAt htop, hn, Nat.cast_zero]
    exact ((hf z hz).analyticOrderAt_eq_zero.mp ho) hfz
  rw [hf.divisor_apply hz, ← Nat.cast_analyticOrderNatAt htop,
    ENat.map_natCast, WithTop.untop₀_coe]
  exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn

/-- Zeros on a compact connected analytic domain are finite when a nonzero value exists. -/
theorem finite_zeros_of_isCompact_of_isPreconnected {f : ℂ → ℂ} {U : Set ℂ} {c : ℂ}
    (hf : AnalyticOnNhd ℂ f U) (hUc : IsCompact U) (hU : IsPreconnected U)
    (hc : c ∈ U) (hfc : f c ≠ 0) : {z ∈ U | f z = 0}.Finite := by
  apply ((divisor f U).finiteSupport hUc).subset
  intro z hz
  change divisor f U z ≠ 0
  exact ne_of_gt (lt_of_lt_of_le (by norm_num : (0 : ℤ) < 1)
    (hf.one_le_divisor_of_zero_of_isPreconnected hU hc hfc hz.1 hz.2))

/-- The number of distinct zeros in any finite subset is at most the full divisor mass. -/
theorem card_zeros_le_sum_divisor {f : ℂ → ℂ} {U : Set ℂ} {c : ℂ}
    (hf : AnalyticOnNhd ℂ f U) (hUc : IsCompact U) (hU : IsPreconnected U)
    (hc : c ∈ U) (hfc : f c ≠ 0) (s : Finset ℂ)
    (hs : ∀ z ∈ s, z ∈ U ∧ f z = 0) :
    (s.card : ℤ) ≤ ∑ᶠ z, divisor f U z := by
  classical
  let D := divisor f U
  let S := (D.finiteSupport hUc).toFinset
  have hpos (z : ℂ) (hz : z ∈ s) : 1 ≤ D z :=
    hf.one_le_divisor_of_zero_of_isPreconnected hU hc hfc (hs z hz).1 (hs z hz).2
  have hsub : s ⊆ S := by
    intro z hz
    apply (D.finiteSupport hUc).mem_toFinset.mpr
    exact ne_of_gt (lt_of_lt_of_le (by norm_num : (0 : ℤ) < 1) (hpos z hz))
  have hsum : (∑ᶠ z, D z) = ∑ z ∈ S, D z :=
    finsum_eq_sum_of_support_subset D (s := S)
      (fun _ hz => (D.finiteSupport hUc).mem_toFinset.mpr hz)
  calc
    (s.card : ℤ) = ∑ _z ∈ s, (1 : ℤ) := by simp
    _ ≤ ∑ z ∈ s, D z := Finset.sum_le_sum hpos
    _ ≤ ∑ z ∈ S, D z := Finset.sum_le_sum_of_subset_of_nonneg hsub
      (fun z _ _ => MeromorphicOn.AnalyticOnNhd.divisor_nonneg hf z)
    _ = ∑ᶠ z, D z := hsum.symm

end AnalyticOnNhd
