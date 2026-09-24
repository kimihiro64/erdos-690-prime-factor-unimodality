/-
Copyright (c) 2026 Jonas Whidden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonas Whidden
-/
import PrimeFactorUnimodality.Mathlib.Analysis.SpecialFunctions.Gamma.StripBound

/-! # Moving Gamma norm bounds to arbitrary vertical strips

At imaginary height of absolute value at least one, each recurrence factor
has norm at least one. Shifting by a natural number therefore bounds Gamma
by a value farther right, where the positive-strip estimate applies.
-/

namespace Complex

/-- Natural right shifts can only increase this bound once `|im z| >= 1`. -/
theorem norm_Gamma_le_norm_Gamma_add_nat {z : ℂ} (hz : 1 ≤ |z.im|) (n : ℕ) :
    ‖Gamma z‖ ≤ ‖Gamma (z + (n : ℂ))‖ := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hnz : z + (n : ℂ) ≠ 0 := by
      intro he
      have hi := congrArg im he
      simp only [add_im, natCast_im, add_zero, zero_im] at hi
      rw [hi, abs_zero] at hz
      norm_num at hz
    have hn : 1 ≤ ‖z + (n : ℂ)‖ :=
      hz.trans (by simpa using abs_im_le_norm (z + (n : ℂ)))
    have hg := congrArg norm (Gamma_add_one (z + (n : ℂ)) hnz)
    rw [norm_mul] at hg
    have hh := mul_le_mul_of_nonneg_right hn (norm_nonneg (Gamma (z + (n : ℂ))))
    rw [one_mul, ← hg] at hh
    exact ih.trans (by simpa only [Nat.cast_add, Nat.cast_one, add_assoc] using hh)

/-- A positive-strip bound controls a translated strip away from its real axis. -/
theorem norm_Gamma_le_max_of_shifted_re_mem_Icc (n : ℕ) {a b : ℝ}
    (ha : 0 < a) (hb : 0 < b) {z : ℂ} (hz : 1 ≤ |z.im|)
    (hre : z.re + (n : ℝ) ∈ Set.Icc a b) :
    ‖Gamma z‖ ≤ max (Real.Gamma a) (Real.Gamma b) :=
  (norm_Gamma_le_norm_Gamma_add_nat hz n).trans
    (norm_Gamma_le_max_of_re_mem_Icc ha hb (by simpa using hre))

end Complex
