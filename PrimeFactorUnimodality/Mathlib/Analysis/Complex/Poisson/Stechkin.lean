/-
Copyright (c) 2026 Jonas Whidden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonas Whidden
-/
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! # Stechkin's paired Poisson-kernel inequality

Pair the two real parts `β` and `1-β` of reflected zeros. If `σ > 1` and
`τ(τ-1) = σ²`, their paired kernels remain nonnegative after subtracting
`1/√5` times the kernel at `τ`. At the zero's height, the whole pole term
`1/(σ-β)` can still be retained. The proof is an explicit polynomial
factorization after clearing positive denominators.

These are the real-variable inequalities in Stechkin's lemma, as stated in
Kadiri, *Explicit zero-free regions for Dedekind zeta functions*, Lemma 2.1:
https://www.cs.uleth.ca/~kadiri/articles/zero-free-region-Dedekind-June07-2011.pdf
-/

namespace Real

noncomputable section

/-- The sum of the two reflected Poisson kernels. -/
def stechkinPair (σ β t : ℝ) : ℝ :=
  (σ - β) / ((σ - β) ^ 2 + t ^ 2) +
    (σ - 1 + β) / ((σ - 1 + β) ^ 2 + t ^ 2)

/-- Stechkin's shifted real part. -/
def stechkinShift (σ : ℝ) : ℝ := (1 + sqrt (1 + 4 * σ ^ 2)) / 2

private theorem pair_den_pos {σ β : ℝ} (hσ : 1 < σ) (hβ₀ : 0 ≤ β) (hβ₁ : β ≤ 1)
    (t : ℝ) : 0 < ((σ - β) ^ 2 + t ^ 2) * ((σ - 1 + β) ^ 2 + t ^ 2) := by
  have ha : 0 < σ - β := by linarith
  have hb : 0 < σ - 1 + β := by linarith
  positivity

private theorem pair_eq {σ β : ℝ} (hσ : 1 < σ) (hβ₀ : 0 ≤ β) (hβ₁ : β ≤ 1)
    (t : ℝ) :
    stechkinPair σ β t = (2 * σ - 1) * ((σ - β) * (σ - 1 + β) + t ^ 2) /
      (((σ - β) ^ 2 + t ^ 2) * ((σ - 1 + β) ^ 2 + t ^ 2)) := by
  have ha : 0 < (σ - β) ^ 2 + t ^ 2 := by
    have : 0 < σ - β := by linarith
    positivity
  have hb : 0 < (σ - 1 + β) ^ 2 + t ^ 2 := by
    have : 0 < σ - 1 + β := by linarith
    positivity
  unfold stechkinPair
  field_simp [ha.ne', hb.ne']
  ring

/-- A stronger normalized pair comparison supplies Stechkin's constant. -/
theorem stechkinPair_normalized_le {σ τ β : ℝ}
    (hσ : 1 < σ) (hτ : 1 < τ) (hrel : τ * (τ - 1) = σ ^ 2)
    (hβ₀ : 0 ≤ β) (hβ₁ : β ≤ 1) (t : ℝ) :
    (2 * σ - 1) / (2 * τ - 1) * stechkinPair τ β t ≤ stechkinPair σ β t := by
  let v := β * (1 - β)
  let u := σ * (σ - 1) + v
  let U := σ ^ 2 + v
  let q := t ^ 2
  let D := ((σ - β) ^ 2 + t ^ 2) * ((σ - 1 + β) ^ 2 + t ^ 2)
  let E := ((τ - β) ^ 2 + t ^ 2) * ((τ - 1 + β) ^ 2 + t ^ 2)
  have hv : 0 ≤ v := mul_nonneg hβ₀ (sub_nonneg.mpr hβ₁)
  have hu : 0 ≤ u := by dsimp [u]; positivity
  have hU : 0 ≤ U := by dsimp [U]; positivity
  have hq : 0 ≤ q := sq_nonneg t
  have hD : 0 < D := pair_den_pos hσ hβ₀ hβ₁ t
  have hE : 0 < E := pair_den_pos hτ hβ₀ hβ₁ t
  have hab : (σ - β) * (σ - 1 + β) = u := by dsimp [u, v]; ring
  have hAB : (τ - β) * (τ - 1 + β) = U := by dsimp [U, v]; nlinarith [hrel]
  have hy : (2 * τ - 1) ^ 2 = 4 * σ ^ 2 + 1 := by nlinarith [hrel]
  have hDform : D = u ^ 2 + ((2 * σ - 1) ^ 2 - 2 * u) * q + q ^ 2 := by
    rw [← hab]
    dsimp [D, q]
    ring
  have hEform : E = U ^ 2 + (4 * σ ^ 2 + 1 - 2 * U) * q + q ^ 2 := by
    rw [← hAB, ← hy]
    dsimp [E, q]
    ring
  have hid : (u + q) * E - (U + q) * D =
      σ * (u * U + ((2 * σ + 1) * (σ - 1) + 6 * v) * q + q ^ 2) := by
    rw [hDform, hEform]
    dsimp [u, U]
    ring
  have hdiff : 0 ≤ (u + q) * E - (U + q) * D := by
    rw [hid]
    have : 0 < σ - 1 := sub_pos.mpr hσ
    positivity
  have hrat : (U + q) / E ≤ (u + q) / D :=
    (div_le_div_iff₀ hE hD).mpr (by linarith)
  rw [pair_eq hσ hβ₀ hβ₁, pair_eq hτ hβ₀ hβ₁, hab, hAB]
  change (2 * σ - 1) / (2 * τ - 1) * ((2 * τ - 1) * (U + q) / E) ≤
    (2 * σ - 1) * (u + q) / D
  have hne : 2 * τ - 1 ≠ 0 := by linarith
  calc
    _ = (2 * σ - 1) * ((U + q) / E) := by field_simp
    _ ≤ (2 * σ - 1) * ((u + q) / D) :=
      mul_le_mul_of_nonneg_left hrat (by linarith)
    _ = _ := by ring

/-- `1/√5` is a uniform permissible coefficient for every `σ > 1`. -/
theorem stechkinPair_le {σ τ β : ℝ}
    (hσ : 1 < σ) (hτ : 1 < τ) (hrel : τ * (τ - 1) = σ ^ 2)
    (hβ₀ : 0 ≤ β) (hβ₁ : β ≤ 1) (t : ℝ) :
    (1 / sqrt 5) * stechkinPair τ β t ≤ stechkinPair σ β t := by
  have h5 : 0 < sqrt 5 := sqrt_pos.mpr (by norm_num)
  have h5sq : sqrt 5 ^ 2 = 5 := sq_sqrt (by norm_num)
  have hy : 0 < 2 * τ - 1 := by linarith
  have hx : 0 < 2 * σ - 1 := by linarith
  have hsq : (2 * τ - 1) ^ 2 ≤ (sqrt 5 * (2 * σ - 1)) ^ 2 := by
    rw [mul_pow, h5sq]
    nlinarith [sq_nonneg (σ - 1)]
  have hr := (sq_le_sq₀ hy.le (mul_pos h5 hx).le).mp hsq
  have hκ : 1 / sqrt 5 ≤ (2 * σ - 1) / (2 * τ - 1) :=
    (div_le_div_iff₀ h5 hy).mpr (by linarith)
  have hp : 0 ≤ stechkinPair τ β t := by
    unfold stechkinPair
    have : 0 < τ - β := by linarith
    have : 0 < τ - 1 + β := by linarith
    positivity
  exact (mul_le_mul_of_nonneg_right hκ hp).trans
    (stechkinPair_normalized_le hσ hτ hrel hβ₀ hβ₁ t)

/-- At the zero's height, the remaining reflected term absorbs the shifted pair. -/
theorem stechkinPair_aligned_le {σ τ β : ℝ}
    (hσ : 1 < σ) (hτ : 1 < τ) (hrel : τ * (τ - 1) = σ ^ 2)
    (hβ₀ : 0 ≤ β) (hβ₁ : β ≤ 1) :
    1 / (σ - β) + (1 / sqrt 5) * stechkinPair τ β 0 ≤ stechkinPair σ β 0 := by
  have hσ0 : 0 < σ := zero_lt_one.trans hσ
  have ha : 0 < σ - β := by linarith
  have hb : 0 < σ - 1 + β := by linarith
  have hA : 0 < τ - β := by linarith
  have hB : 0 < τ - 1 + β := by linarith
  have h5 : 0 < sqrt 5 := sqrt_pos.mpr (by norm_num)
  have h5sq : sqrt 5 ^ 2 = 5 := sq_sqrt (by norm_num)
  have hy : 0 < 2 * τ - 1 := by linarith
  have hsq : (2 * τ - 1) ^ 2 ≤ (sqrt 5 * σ) ^ 2 := by
    rw [mul_pow, h5sq]
    nlinarith [sq_nonneg (σ - 1)]
  have hr := (sq_le_sq₀ hy.le (mul_pos h5 hσ0).le).mp hsq
  have hv : 0 ≤ β * (1 - β) := mul_nonneg hβ₀ (sub_nonneg.mpr hβ₁)
  have hprod : (τ - β) * (τ - 1 + β) = σ ^ 2 + β * (1 - β) := by nlinarith [hrel]
  have hκ : (2 * τ - 1) / (sqrt 5 * ((τ - β) * (τ - 1 + β))) ≤ 1 / σ := by
    apply (div_le_div_iff₀ (mul_pos h5 (mul_pos hA hB)) hσ0).mpr
    rw [hprod]
    nlinarith [mul_le_mul_of_nonneg_right hr hσ0.le, mul_nonneg h5.le hv]
  have hi : 1 / σ ≤ 1 / (σ - 1 + β) := one_div_le_one_div_of_le hb (by linarith)
  have hpτ : (1 / sqrt 5) * stechkinPair τ β 0 =
      (2 * τ - 1) / (sqrt 5 * ((τ - β) * (τ - 1 + β))) := by
    unfold stechkinPair
    field_simp [hA.ne', hB.ne']
    ring
  have hpσ : stechkinPair σ β 0 = 1 / (σ - β) + 1 / (σ - 1 + β) := by
    unfold stechkinPair
    field_simp [ha.ne', hb.ne']
    ring
  rw [hpτ, hpσ]
  exact add_le_add le_rfl (hκ.trans hi)

/-- The canonical shift satisfies the algebraic equation used in the kernel comparison. -/
theorem stechkinShift_spec {σ : ℝ} (hσ : 1 < σ) :
    1 < stechkinShift σ ∧ stechkinShift σ * (stechkinShift σ - 1) = σ ^ 2 := by
  have hs : sqrt (1 + 4 * σ ^ 2) ^ 2 = 1 + 4 * σ ^ 2 := sq_sqrt (by positivity)
  have hp := sqrt_nonneg (1 + 4 * σ ^ 2)
  unfold stechkinShift
  constructor <;> nlinarith

end

end Real
