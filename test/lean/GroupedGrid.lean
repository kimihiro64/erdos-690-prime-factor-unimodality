import Mathlib.Tactic.FinCases
import PrimeFactorUnimodality.Mathlib.Analysis.Fourier.GroupedGrid

/-! # Radix/grid interfaces, collisions and boundary cases -/

set_option autoImplicit false

namespace PrimeFactorUnimodality.Tests

noncomputable section

open Complex Finset Fourier ZMod



example (n : ℕ) (B : Finset ℤ) (a : ℤ → ℂ) (k : ZMod (2 ^ n)) :
    (aliasVector n B a)[k.val]'(ZMod.val_lt k) = aliasCoefficients B a k := by
  exact Fourier.aliasVector_get n B a k

example {n : ℕ} {t : RadixTrace n}
    {B : Finset ℤ} {a : ℤ → ℂ}
    (ht : t.Valid (stdAddChar (1 : ZMod (2 ^ n))) (aliasVector n B a))
    (k : ZMod (2 ^ n)) :
    ‖dft (aliasCoefficients B a) (-k) - t.values[k.val]'(val_lt k)‖ ≤ t.error := by
  exact Fourier.RadixTrace.Valid.norm_dft_alias_sub_le ht k

example (n m : ℕ) (B : Finset ℤ)
    (a : ℤ → ℕ → ℂ) (t : ℕ → RadixTrace n)
    (ht : ∀ j ∈ range m,
      (t j).Valid (stdAddChar (1 : ZMod (2 ^ n))) (aliasVector n B (fun b => a b j)))
    (k : ℤ) :
    ‖(∑ b ∈ B, exp (I * (((2 * Real.pi * k / (2 ^ n)) * b : ℝ) : ℂ)) *
        ∑ j ∈ range m, a b j * ((2 * Real.pi * k / (2 ^ n) : ℝ) : ℂ) ^ j) -
      ∑ j ∈ range m, (t j).values[(k : ZMod (2 ^ n)).val]'(val_lt _) *
        ((2 * Real.pi * k / (2 ^ n) : ℝ) : ℂ) ^ j‖ ≤
      ∑ j ∈ range m, (t j).error * |2 * Real.pi * k / (2 ^ n)| ^ j := by
  exact Fourier.norm_exp_polynomial_grid_sub_traces_le n m B a t ht k

example (n : ℕ) (a : ℤ → ℂ) (k : ZMod (2 ^ n)) :
    (aliasVector n ∅ a)[k.val]'(val_lt k) = 0 := by
  rw [aliasVector_get]
  simp [aliasCoefficients]

example : (aliasVector 0 {-2, 0, 3} (fun _ => (1 : ℂ)))[0] = 3 := by
  have h := aliasVector_get 0 {-2, 0, 3} (fun _ => (1 : ℂ)) 0
  have hz (b : ℤ) : (b : ZMod 1) = 0 := Subsingleton.elim _ _
  norm_num [aliasCoefficients, hz] at h
  exact h

end

end PrimeFactorUnimodality.Tests
