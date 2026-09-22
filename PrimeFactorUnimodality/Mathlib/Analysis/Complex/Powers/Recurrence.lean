/-
Copyright (c) 2026 Jonas Whidden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonas Whidden
-/
import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Topology.MetricSpace.Sequences

/-! # Large powers returning to the positive real axis

Compactness of the unit circle gives a convergent subsequence of powers.
Taking widely separated differences of its exponents gives powers tending
to one, with exponents tending to infinity. Every nonzero complex number
therefore has arbitrarily large powers whose real parts are at least half
their norms. No irrationality or non-torsion assumption is needed.
-/

namespace Complex

open Filter Metric
open scoped Topology

/-- Unit complex numbers have powers tending to one along unbounded exponents. -/
theorem exists_pow_tendsto_one_of_norm_eq_one {u : ℂ} (hu : ‖u‖ = 1) :
    ∃ q : ℕ → ℕ, Tendsto q atTop atTop ∧
      Tendsto (fun n => u ^ q n) atTop (𝓝 1) := by
  have hu0 : u ≠ 0 := by intro h; simp [h] at hu
  obtain ⟨w, hw, φ, hφ, hl⟩ := (isCompact_sphere (0 : ℂ) 1).tendsto_subseq
    (x := fun n : ℕ => u ^ n) (fun n => by simp [norm_pow, hu])
  have hw0 : w ≠ 0 := by intro h; simp [h] at hw
  let q (n : ℕ) := φ (n + n) - φ n
  have hq (n : ℕ) : n ≤ q n := by
    apply Nat.le_sub_of_add_le
    simpa only [Nat.add_comm] using hφ.add_le_nat n n
  have hdouble : Tendsto (fun n : ℕ => n + n) atTop atTop :=
    tendsto_atTop_mono (fun n => Nat.le_add_right n n) tendsto_id
  have hquot := (hl.comp hdouble).div hl hw0
  refine ⟨q, tendsto_atTop_mono hq tendsto_id, ?_⟩
  rw [div_self hw0] at hquot
  apply hquot.congr'
  apply Eventually.of_forall
  intro n
  exact (pow_sub₀ u hu0 (hφ.monotone (Nat.le_add_right n n))).symm

/-- Infinitely many powers of a unit complex number have real part at least one half. -/
theorem frequently_half_le_re_pow_of_norm_eq_one {u : ℂ} (hu : ‖u‖ = 1) :
    ∃ᶠ n : ℕ in atTop, (1 / 2 : ℝ) ≤ (u ^ n).re := by
  obtain ⟨q, hq, hp⟩ := exists_pow_tendsto_one_of_norm_eq_one hu
  have hRe := ((continuous_re.tendsto (1 : ℂ)).comp hp).eventually
    (eventually_gt_nhds (by norm_num : (1 / 2 : ℝ) < (1 : ℂ).re))
  apply frequently_atTop.mpr
  intro N
  obtain ⟨k, hk, hk'⟩ := ((hq.eventually_ge_atTop N).and hRe).exists
  exact ⟨q k, hk, hk'.le⟩

/-- Nonzero complex numbers have arbitrarily large powers with a quantitative positive real part. -/
theorem frequently_half_norm_pow_le_re_pow {z : ℂ} (hz : z ≠ 0) :
    ∃ᶠ n : ℕ in atTop, ‖z‖ ^ n / 2 ≤ (z ^ n).re := by
  have hn : 0 < ‖z‖ := norm_pos_iff.mpr hz
  have hu : ‖z / (‖z‖ : ℂ)‖ = 1 := by
    simp [hn.ne']
  apply (frequently_half_le_re_pow_of_norm_eq_one hu).mono
  intro n h
  have heq : ((z / (‖z‖ : ℂ)) ^ n).re = (z ^ n).re / ‖z‖ ^ n := by
    rw [div_pow, ← ofReal_pow, div_ofReal_re]
  rw [heq] at h
  have hmul := (le_div_iff₀ (pow_pos hn n)).mp h
  simpa only [one_div, inv_mul_eq_div] using hmul

end Complex
