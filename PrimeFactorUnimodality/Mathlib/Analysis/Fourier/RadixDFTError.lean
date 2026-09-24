/-
Copyright (c) 2026 Jonas Whidden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonas Whidden
-/
import PrimeFactorUnimodality.Mathlib.Analysis.Fourier.ConvolutionError
import PrimeFactorUnimodality.Mathlib.Analysis.Fourier.RadixError

/-! # Forward and normalized inverse DFT enclosures from shared radix traces

The positive-phase trace evaluates the DFT at the negative index. Input error
is summed before adding the trace's internal rounding; inverse normalization
retains a uniform input error and divides only the trace error by the length.
-/

namespace Fourier

noncomputable section

variable {n : ℕ} {t : RadixTrace n} {q : Vector ℂ (2 ^ n)}

/-- Positive-phase output `j` encloses the DFT at `-j`. -/
theorem RadixTrace.Valid.norm_dft_neg_sub_le
    (ht : t.Valid (ZMod.stdAddChar (1 : ZMod (2 ^ n))) q) (j : ZMod (2 ^ n)) :
    ‖ZMod.dft (fun l : ZMod (2 ^ n) => q[l.val]'(ZMod.val_lt l)) (-j) -
      t.values[j.val]'(ZMod.val_lt j)‖ ≤ t.error := by
  have hs := ht.norm_radixTwo_sub_le (by simp [ZMod.stdAddChar_apply])
    ⟨j.val, ZMod.val_lt j⟩
  rw [ZMod.radixTwo_eq_dft] at hs
  simpa only [ZMod.natCast_zmod_val] using hs

/-- An enclosed input array and one shared trace supply every forward DFT value. -/
theorem RadixTrace.Valid.norm_dft_sub_le
    (ht : t.Valid (ZMod.stdAddChar (1 : ZMod (2 ^ n))) q)
    {a : ZMod (2 ^ n) → ℂ} {ε : ZMod (2 ^ n) → ℝ}
    (ha : ∀ l, ‖a l - q[l.val]'(ZMod.val_lt l)‖ ≤ ε l) (j : ZMod (2 ^ n)) :
    ‖ZMod.dft a j - t.values[(-j).val]'(ZMod.val_lt (-j))‖ ≤
      (∑ l : ZMod (2 ^ n), ε l) + t.error := by
  have hs := ht.norm_dft_neg_sub_le (-j)
  rw [neg_neg] at hs
  exact (norm_sub_le_norm_sub_add_norm_sub _
    (ZMod.dft (fun l : ZMod (2 ^ n) => q[l.val]'(ZMod.val_lt l)) j) _).trans
      (add_le_add (ZMod.norm_dft_sub_le_sum ha j) hs)

/-- One inverse trace encloses the normalized transform of enclosed frequency inputs. -/
theorem RadixTrace.Valid.norm_inv_dft_sub_le
    (ht : t.Valid (ZMod.stdAddChar (1 : ZMod (2 ^ n))) q)
    {a : ZMod (2 ^ n) → ℂ} {ε : ℝ}
    (ha : ∀ l, ‖a l - q[l.val]'(ZMod.val_lt l)‖ ≤ ε) (j : ZMod (2 ^ n)) :
    ‖((2 ^ n : ℕ) : ℂ)⁻¹ * ZMod.dft a (-j) -
      ((2 ^ n : ℕ) : ℂ)⁻¹ * t.values[j.val]'(ZMod.val_lt j)‖ ≤
      ε + t.error / (2 ^ n : ℕ) :=
  ZMod.norm_inv_dft_sub_rounded_le ha j (ht.norm_dft_neg_sub_le j)

end

end Fourier
