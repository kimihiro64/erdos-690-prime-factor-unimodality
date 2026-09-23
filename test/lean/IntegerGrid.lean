import Mathlib.Tactic.FinCases
import PrimeFactorUnimodality.Mathlib.Analysis.Fourier.IntegerGrid

/-! # Radix/grid interfaces, collisions and boundary cases -/

set_option autoImplicit false

namespace PrimeFactorUnimodality.Tests

noncomputable section

open Complex Finset Fourier ZMod

variable {N : ℕ} [NeZero N]

example (j : ℕ) :
    stdAddChar (1 : ZMod N) ^ j = stdAddChar (j : ZMod N) := by
  exact ZMod.stdAddChar_one_pow j

example : stdAddChar (1 : ZMod N) ^ N = 1 := by
  exact ZMod.stdAddChar_one_pow_card

example (i : Fin N) : (finEquiv N i).val = i.val := by
  exact ZMod.val_finEquiv i

example (i : Fin N) : finEquiv N i = (i.val : ZMod N) := by
  exact ZMod.finEquiv_eq_natCast i

example (n : ℕ) (a : Vector ℂ (2 ^ n)) (k : Fin (2 ^ n)) :
    (Fourier.radixTwo n (stdAddChar (1 : ZMod (2 ^ n))) a)[k.val] =
      dft (fun j : ZMod (2 ^ n) => a[j.val]'(val_lt j)) (-(k.val : ZMod (2 ^ n))) := by
  exact ZMod.radixTwo_eq_dft n a k

example (B : Finset ℤ) (a : ℤ → ℂ) (k : ZMod N) :
    dft (aliasCoefficients B a) (-k) = ∑ b ∈ B, stdAddChar ((b : ZMod N) * k) * a b := by
  exact ZMod.dft_alias_neg B a k

example (b k : ℤ) :
    stdAddChar ((b : ZMod N) * (k : ZMod N)) =
      exp (I * (((2 * Real.pi * k / N) * b : ℝ) : ℂ)) := by
  exact ZMod.stdAddChar_grid b k

example (B : Finset ℤ) (a : ℤ → ℂ) (k : ℤ) :
    (∑ b ∈ B, exp (I * (((2 * Real.pi * k / N) * b : ℝ) : ℂ)) * a b) =
      dft (aliasCoefficients B a) (-(k : ZMod N)) := by
  exact ZMod.sum_exp_grid_eq_dft B a k

example (B : Finset ℤ) (a : ℤ → ℕ → ℂ) (m : ℕ) (k : ℤ) :
    (∑ b ∈ B, exp (I * (((2 * Real.pi * k / N) * b : ℝ) : ℂ)) *
      ∑ j ∈ range m, a b j * ((2 * Real.pi * k / N : ℝ) : ℂ) ^ j) =
      ∑ j ∈ range m, dft (aliasCoefficients B (fun b => a b j)) (-(k : ZMod N)) *
        ((2 * Real.pi * k / N : ℝ) : ℂ) ^ j := by
  exact ZMod.sum_exp_polynomial_grid_eq B a m k

example : aliasCoefficients (N := 1) {-2, 0, 3} (fun _ => (1 : ℂ)) 0 = 3 := by
  have hz (b : ℤ) : (b : ZMod 1) = 0 := Subsingleton.elim _ _
  norm_num [aliasCoefficients, hz]

example (k : ZMod 8) : dft (aliasCoefficients (∅ : Finset ℤ) (fun _ => (1 : ℂ))) (-k) = 0 := by
  rw [dft_alias_neg]
  simp

end

end PrimeFactorUnimodality.Tests
