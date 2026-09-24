import PrimeFactorUnimodality.Mathlib.Data.Nat.BitProduct

/-! # Balanced selected products: clipping, offsets and generic monoid semantics -/

set_option autoImplicit false

section

variable {M : Type*} [CommMonoid M]

example (f : ℕ → M) (k start bits : ℕ) :
    Nat.bitProductPow f k start bits =
      ∏ i ∈ Finset.range (2 ^ k), if bits.testBit i then f (start + i) else 1 :=
  Nat.bitProductPow_eq_prod f k start bits

example (f : ℕ → M) (bits start a b : ℕ) :
    Nat.bitProductRange f bits start (a + b) =
      Nat.bitProductRange f bits start a * Nat.bitProductRange f bits (start + a) b :=
  Nat.bitProductRange_add f bits start a b

example (f : ℕ → M) (k bits start width : ℕ) (hw : width ≤ 2 ^ k) :
    Nat.bitProductBlock f k bits start width = Nat.bitProductRange f bits start width :=
  Nat.bitProductBlock_eq_range f k bits start width hw

end

example : Nat.bitProductBlock (fun i => i + 1) 2 13 0 4 = 12 := by decide +kernel
example : Nat.bitProductBlock (fun i => i + 1) 1 13 2 2 = 12 := by decide +kernel
example : Nat.bitProductBlock (fun i => i + 1) 0 13 2 2 = 3 := by decide +kernel
example : Nat.bitProductBlock (fun i => i + 1) 3 13 2 0 = 1 := by decide +kernel
example : Nat.bitProductBlock (fun i => i + 1) 2 13 4 4 = 1 := by decide +kernel
example : Nat.bitProductBlock (fun i => i + 1) 2 0 0 4 = 1 := by decide +kernel
example : Nat.bitProductBlock id 2 13 0 4 = 0 := by decide +kernel
