/-
Copyright (c) 2026 Jonas Whidden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonas Whidden
-/
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring
import PrimeFactorUnimodality.Mathlib.Analysis.Meromorphic.SimplePoleLimit

/-! # Gamma residues at every nonpositive integer

The residue at zero and the functional equation prove all residue limits by
induction. Affine transport retains the inverse derivative factor. The entire
reciprocal also gives meromorphicity, so the limits identify actual simple poles.
-/

open Filter
open scoped Topology

namespace Complex

/-- Gamma is meromorphic everywhere, since its reciprocal is entire. -/
theorem meromorphicAt_Gamma (s : ℂ) : MeromorphicAt Gamma s := by
  have hi := (differentiable_one_div_Gamma.analyticAt s).meromorphicAt
  have hh : MeromorphicAt (fun z : ℂ => ((Gamma z)⁻¹)⁻¹) s := hi.inv
  simpa only [inv_inv] using hh

/-- Away from the nonpositive integers, Gamma is analytic. -/
theorem analyticAt_Gamma_of_not_pole {s : ℂ} (hs : ∀ n : ℕ, s ≠ -(n : ℂ)) :
    AnalyticAt ℂ Gamma s :=
  (meromorphicAt_Gamma s).analyticAt (continuousAt_Gamma s hs)

/-- Translation to zero expresses all Gamma residue limits in one induction. -/
theorem tendsto_mul_Gamma_sub_nat (n : ℕ) :
    Tendsto (fun z : ℂ => z * Gamma (z - (n : ℂ))) (𝓝[≠] 0)
      (𝓝 (((-1 : ℂ) ^ n) / (n.factorial : ℂ))) := by
  induction n with
  | zero => simpa using tendsto_self_mul_Gamma_nhds_zero
  | succ n ih =>
    have hn : -((n : ℂ) + 1) ≠ 0 := by
      have hpos : (0 : ℝ) < n + 1 := by positivity
      intro he
      have hr := congrArg re he
      norm_num at hr
      linarith
    have hd : Tendsto (fun z : ℂ => z - ((n : ℂ) + 1)) (𝓝[≠] 0)
        (𝓝 (-((n : ℂ) + 1))) := by
      have hi : Tendsto (fun z : ℂ => z) (𝓝[≠] 0) (𝓝 0) :=
        tendsto_nhdsWithin_of_tendsto_nhds tendsto_id
      simpa using hi.sub_const ((n : ℂ) + 1)
    have hl := ih.div hd hn
    have he : ((-1 : ℂ) ^ n / (n.factorial : ℂ)) / (-((n : ℂ) + 1)) =
        (-1 : ℂ) ^ (n + 1) / ((n + 1).factorial : ℂ) := by
      rw [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one, pow_succ]
      field_simp
    rw [he] at hl
    apply hl.congr'
    filter_upwards [hd.eventually_ne hn] with z hz
    have hg := Gamma_add_one (z - ((n : ℂ) + 1)) hz
    have ha : z - ((n : ℂ) + 1) + 1 = z - (n : ℂ) := by ring
    rw [ha] at hg
    dsimp only [Pi.div_apply]
    rw [hg]
    push_cast
    field_simp

/-- Gamma has residue `(-1)^n/n!` at `-n`. -/
theorem tendsto_add_nat_mul_Gamma (n : ℕ) :
    Tendsto (fun z : ℂ => (z + (n : ℂ)) * Gamma z) (𝓝[≠] (-(n : ℂ)))
      (𝓝 (((-1 : ℂ) ^ n) / (n.factorial : ℂ))) := by
  have ht : Tendsto (fun z : ℂ => z + (n : ℂ)) (𝓝[≠] (-(n : ℂ))) (𝓝[≠] 0) := by
    apply tendsto_nhdsWithin_iff.mpr
    constructor
    · have hi : Tendsto (fun z : ℂ => z) (𝓝[≠] (-(n : ℂ))) (𝓝 (-(n : ℂ))) :=
        tendsto_nhdsWithin_of_tendsto_nhds tendsto_id
      simpa using hi.add_const (n : ℂ)
    · filter_upwards [self_mem_nhdsWithin] with z hz
      change z + (n : ℂ) ≠ 0
      change z ≠ -(n : ℂ) at hz
      exact fun he => hz (eq_neg_of_add_eq_zero_left he)
  simpa only [Function.comp_def, add_sub_cancel_right] using
    (tendsto_mul_Gamma_sub_nat n).comp ht

/-- An affine change of variable contributes the inverse of its nonzero slope. -/
theorem tendsto_sub_mul_Gamma_affine (n : ℕ) {a b p : ℂ} (ha : a ≠ 0)
    (hp : a * p + b = -(n : ℂ)) :
    Tendsto (fun z : ℂ => (z - p) * Gamma (a * z + b)) (𝓝[≠] p)
      (𝓝 (((-1 : ℂ) ^ n / (n.factorial : ℂ)) / a)) := by
  have ht : Tendsto (fun z : ℂ => a * z + b) (𝓝[≠] p) (𝓝[≠] (-(n : ℂ))) := by
    apply tendsto_nhdsWithin_iff.mpr
    constructor
    · rw [← hp]
      exact (show ContinuousAt (fun z : ℂ => a * z + b) p by fun_prop).continuousWithinAt.tendsto
    · filter_upwards [self_mem_nhdsWithin] with z hz
      change a * z + b ≠ -(n : ℂ)
      change z ≠ p at hz
      intro he
      apply hz
      exact mul_left_cancel₀ ha (add_right_cancel (he.trans hp.symm))
  have hl := ((tendsto_add_nat_mul_Gamma n).comp ht).div_const a
  apply hl.congr'
  apply Eventually.of_forall
  intro z
  dsimp only [Function.comp_apply]
  have he : a * z + b + (n : ℂ) = a * (z - p) := by linear_combination hp
  rw [he]
  field_simp

/-- The nonzero Gamma residue forces meromorphic order exactly `-1`. -/
theorem meromorphicOrderAt_Gamma_neg_nat (n : ℕ) :
    meromorphicOrderAt Gamma (-(n : ℂ)) = (-1 : ℤ) := by
  apply (meromorphicAt_Gamma _).order_eq_neg_one_of_tendsto
    (c := (-1 : ℂ) ^ n / (n.factorial : ℂ))
    (div_ne_zero (pow_ne_zero _ (by norm_num)) (by exact_mod_cast Nat.factorial_ne_zero n))
  simpa only [sub_neg_eq_add] using tendsto_add_nat_mul_Gamma n

end Complex
