/-
Copyright (c) 2026 Jonas Whidden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonas Whidden
-/
import PrimeFactorUnimodality.Mathlib.Analysis.Fourier.IntegerGrid
import PrimeFactorUnimodality.Mathlib.Analysis.SpecialFunctions.Complex.GroupedRounding

/-! # Shared radix computation traces with complete rounding bounds

The input vector is supplied once; recursive children use its even and odd
projections. Every merge stores its output and twiddle arrays once, with
uniform local enclosures. Recursive validity covers every leaf and output.
The assembler retains input, twiddle and arithmetic errors at all levels.
-/

namespace Fourier

noncomputable section

open Complex

/-- A shared computation tree, with no independently duplicated proof per output. -/
inductive RadixTrace : ℕ → Type
  | leaf (value : ℂ) (error : ℝ) : RadixTrace 0
  | node {n : ℕ} (even odd : RadixTrace n)
      (output twiddle : Vector ℂ (2 ^ (n + 1)))
      (rounding phaseError rightCap : ℝ) : RadixTrace (n + 1)

/-- Only the current node's output is exposed to its parent. -/
def RadixTrace.values : {n : ℕ} → RadixTrace n → Vector ℂ (2 ^ n)
  | 0, .leaf value _ => Vector.singleton value
  | _ + 1, .node _ _ output _ _ _ _ => output

/-- A complete uniform error, including both child computations. -/
def RadixTrace.error : {n : ℕ} → RadixTrace n → ℝ
  | 0, .leaf _ error => error
  | _ + 1, .node l r _ _ ε δ M => l.error + r.error + M * δ + ε

/-- Local checks and complete recursive coverage for one shared input vector. -/
def RadixTrace.Valid : {n : ℕ} → RadixTrace n → ℂ → Vector ℂ (2 ^ n) → Prop
  | 0, .leaf value error, _, a => ‖a[0] - value‖ ≤ error
  | n + 1, .node l r out tw ε δ M, w, a =>
    l.Valid (w ^ 2) (evenSamples n a) ∧ r.Valid (w ^ 2) (oddSamples n a) ∧
    0 ≤ δ ∧ (∀ k : Fin (2 ^ (n + 1)), ‖w ^ k.val - tw[k.val]‖ ≤ δ) ∧
    (∀ k : Fin (2 ^ n), ‖r.values[k.val]‖ ≤ M) ∧
    ∀ k : Fin (2 ^ (n + 1)),
      ‖l.values[k.val % (2 ^ n)]'(Nat.mod_lt _ (by positivity)) +
        tw[k.val] * r.values[k.val % (2 ^ n)]'(Nat.mod_lt _ (by positivity)) -
          out[k.val]‖ ≤ ε

/-- One induction assembles every local enclosure into all exact algorithm outputs. -/
theorem RadixTrace.Valid.norm_radixTwo_sub_le {n : ℕ} {t : RadixTrace n}
    {w : ℂ} {a : Vector ℂ (2 ^ n)} (ht : t.Valid w a) (hw : ‖w‖ = 1)
    (k : Fin (2 ^ n)) : ‖(radixTwo n w a)[k.val] - t.values[k.val]‖ ≤ t.error := by
  induction t generalizing w with
  | leaf value error =>
    simpa [radixTwo, RadixTrace.Valid, RadixTrace.values, RadixTrace.error] using ht
  | @node n l r out tw ε δ M ihl ihr =>
    rcases ht with ⟨hl, hr, hδ, htw, hM, hout⟩
    let j : Fin (2 ^ n) := ⟨k.val % (2 ^ n), Nat.mod_lt _ (by positivity)⟩
    have hw₂ : ‖w ^ 2‖ = 1 := by simp [hw]
    have he := ihl hl hw₂ j
    have ho := ihr hr hw₂ j
    have hm := norm_unit_mul_sub_mul_le (p := w ^ k.val) (by simp [hw])
      ((radixTwo n (w ^ 2) (oddSamples n a))[j.val]) (r.values[j.val]) (tw[k.val])
    have hm' : ‖w ^ k.val * (radixTwo n (w ^ 2) (oddSamples n a))[j.val] -
        tw[k.val] * r.values[j.val]‖ ≤ r.error + M * δ :=
      hm.trans (add_le_add ho ((mul_le_mul_of_nonneg_left (htw k) (norm_nonneg _)).trans
        (mul_le_mul_of_nonneg_right (hM j) hδ)))
    have hsum : ‖(radixTwo n (w ^ 2) (evenSamples n a))[j.val] +
        w ^ k.val * (radixTwo n (w ^ 2) (oddSamples n a))[j.val] -
        (l.values[j.val] + tw[k.val] * r.values[j.val])‖ ≤ l.error + (r.error + M * δ) := by
      rw [add_sub_add_comm]
      exact (norm_add_le _ _).trans (add_le_add he hm')
    have hall := (norm_sub_le_norm_sub_add_norm_sub
      ((radixTwo n (w ^ 2) (evenSamples n a))[j.val] +
        w ^ k.val * (radixTwo n (w ^ 2) (oddSamples n a))[j.val])
      (l.values[j.val] + tw[k.val] * r.values[j.val]) (out[k.val])).trans
        (add_le_add hsum (hout k))
    have hpower := powerTable_get w (2 ^ (n + 1)) ⟨k.val, by have := k.isLt; omega⟩
    simpa only [radixTwo, Vector.getElem_ofFn, hpower, RadixTrace.values,
      RadixTrace.error, j, add_assoc] using hall

/-- A checked shared trace encloses the complete mathematical Fourier sum. -/
theorem RadixTrace.Valid.norm_sum_sub_le {n : ℕ} {t : RadixTrace n}
    {w : ℂ} {a : Vector ℂ (2 ^ n)} (ht : t.Valid w a) (hw : ‖w‖ = 1)
    (hperiod : w ^ (2 ^ n) = 1) (k : Fin (2 ^ n)) :
    ‖(∑ j : Fin (2 ^ n), a[j.val] * w ^ (k.val * j.val)) - t.values[k.val]‖ ≤ t.error := by
  rw [← radixTwo_get n w hperiod]
  exact ht.norm_radixTwo_sub_le hw k

end

end Fourier
