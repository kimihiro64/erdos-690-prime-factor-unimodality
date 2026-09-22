/-
Copyright (c) 2026 Jonas Whidden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonas Whidden
-/
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Data.Int.Interval
import Mathlib.Data.Set.Card
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! # Change of a continuous phase bounded by its cosine zeros

Every level `pi/2+k*pi` between the endpoint phases is attained by the
intermediate value theorem. Distinct levels require distinct cosine zeros.
Counting these levels bounds the absolute endpoint change, including for
decreasing or nonmonotone phases. This is an endpoint-change estimate, not
a claim about total variation along an oscillating path.
-/

open Real Set

namespace ContinuousOn

/-- Cosine zeros in a finite set bound the increase of a continuous real phase. -/
theorem sub_le_card_add_one_mul_pi_of_cos_eq_zero {f : ℝ → ℝ} {a b : ℝ}
    (hf : ContinuousOn f (Icc a b)) (hab : a ≤ b) (s : Finset ℝ)
    (hs : ∀ x ∈ Icc a b, Real.cos (f x) = 0 → x ∈ s) :
    f b - f a ≤ (s.card + 1 : ℝ) * Real.pi := by
  classical
  by_cases horder : f a ≤ f b
  · let u := (f a - Real.pi / 2) / Real.pi
    let v := (f b - Real.pi / 2) / Real.pi
    have huv : u ≤ v := div_le_div_of_nonneg_right (sub_le_sub_right horder _) Real.pi_pos.le
    let K := Finset.Ioc ⌊u⌋ ⌊v⌋
    let g : ℤ → ℝ := fun k => Real.pi / 2 + (k : ℝ) * Real.pi
    have hg : Function.Injective g := by
      intro k l h
      have he : (k : ℝ) = l := by dsimp [g] at h; nlinarith [Real.pi_pos]
      exact_mod_cast he
    have hsub : K.image g ⊆ s.image f := by
      intro y hy
      obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hy
      have hk' : ⌊u⌋ < k ∧ k ≤ ⌊v⌋ := Finset.mem_Ioc.mp hk
      have hlu : u < (k : ℝ) := (Int.floor_lt).mp hk'.1
      have hlv : (k : ℝ) ≤ v := (Int.le_floor).mp hk'.2
      have hleft : f a ≤ g k := by
        have h := (div_lt_iff₀ Real.pi_pos).mp hlu
        dsimp [g]
        linarith
      have hright : g k ≤ f b := by
        have h := (le_div_iff₀ Real.pi_pos).mp hlv
        dsimp [g]
        linarith
      obtain ⟨x, hx, heq⟩ := intermediate_value_Icc hab hf ⟨hleft, hright⟩
      refine Finset.mem_image.mpr ⟨x, hs x hx ?_, heq⟩
      rw [heq]
      simp [g, Real.cos_add_int_mul_pi]
    have hcard : K.card ≤ s.card := by
      calc
        K.card = (K.image g).card := (Finset.card_image_of_injective _ hg).symm
        _ ≤ (s.image f).card := Finset.card_le_card hsub
        _ ≤ s.card := Finset.card_image_le
    have hK : (K.card : ℤ) = ⌊v⌋ - ⌊u⌋ := Int.card_Ioc_of_le _ _ (Int.floor_mono huv)
    have hKreal : (K.card : ℝ) = (⌊v⌋ : ℝ) - (⌊u⌋ : ℝ) := by exact_mod_cast hK
    have hwidth : v - u ≤ (s.card : ℝ) + 1 := by
      have hcv : (K.card : ℝ) ≤ (s.card : ℝ) := by exact_mod_cast hcard
      linarith [Int.floor_le u, Int.lt_floor_add_one v]
    have hmul := mul_le_mul_of_nonneg_right hwidth Real.pi_pos.le
    have heq : (v - u) * Real.pi = f b - f a := by
      dsimp [u, v]
      field_simp
      ring
    rwa [heq] at hmul
  · have hright : 0 ≤ (s.card + 1 : ℝ) * Real.pi :=
      mul_nonneg (by positivity) Real.pi_pos.le
    exact (sub_nonpos.mpr (le_of_not_ge horder)).trans hright

/-- A finite set containing the cosine zeros bounds the absolute endpoint phase change. -/
theorem abs_sub_le_card_add_one_mul_pi_of_cos_eq_zero {f : ℝ → ℝ} {a b : ℝ}
    (hf : ContinuousOn f (Icc a b)) (hab : a ≤ b) (s : Finset ℝ)
    (hs : ∀ x ∈ Icc a b, Real.cos (f x) = 0 → x ∈ s) :
    |f b - f a| ≤ (s.card + 1 : ℝ) * Real.pi := by
  apply abs_le.mpr
  refine ⟨?_, hf.sub_le_card_add_one_mul_pi_of_cos_eq_zero hab s hs⟩
  have h := hf.neg.sub_le_card_add_one_mul_pi_of_cos_eq_zero hab s (by simpa using hs)
  dsimp at h
  linarith

/-- The actual finite cosine-zero set controls the endpoint change of a continuous phase. -/
theorem abs_sub_le_ncard_add_one_mul_pi_of_cos_eq_zero {f : ℝ → ℝ} {a b : ℝ}
    (hf : ContinuousOn f (Icc a b)) (hab : a ≤ b)
    (hz : {x ∈ Icc a b | Real.cos (f x) = 0}.Finite) :
    |f b - f a| ≤ ({x ∈ Icc a b | Real.cos (f x) = 0}.ncard + 1 : ℝ) * Real.pi := by
  classical
  rw [Set.ncard_eq_toFinset_card _ hz]
  exact hf.abs_sub_le_card_add_one_mul_pi_of_cos_eq_zero hab hz.toFinset
    (fun x hx hcos => hz.mem_toFinset.mpr ⟨hx, hcos⟩)

end ContinuousOn
