import PrimeFactorUnimodality.Mathlib.Analysis.Fourier.RationalAlias

/-! # Rational checks and exact interface regressions -/

set_option autoImplicit false

namespace PrimeFactorUnimodality.Tests

noncomputable section

open Complex Finset Fourier ZMod

example (n : ℕ) (rows : List ℤ) (a : ℤ → ℚ)
    (k : ZMod (2 ^ n)) :
    (rationalAliasCoordinate n rows a)[k.val]'(val_lt k) =
      (rows.map (fun b : ℤ => if (b : ZMod (2 ^ n)) = k then a b else 0)).sum := by
  exact Fourier.rationalAliasCoordinate_get n rows a k

example (n : ℕ) (rows : List ℤ) (hr : rows.Nodup)
    (a : ℤ → RationalPoint) :
    (rationalAliasVector n rows a).map RationalPoint.toComplex =
      aliasVector n rows.toFinset (fun b => (a b).toComplex) := by
  exact Fourier.rationalAliasVector_map n rows hr a

example : rationalAliasVector 1 [0, 2, -2] (fun _ => ⟨1, 2⟩) =
    #v[⟨3, 6⟩, ⟨0, 0⟩] := by decide +kernel
example : rationalAliasVector 0 [] (fun _ => ⟨1, 2⟩) = #v[⟨0, 0⟩] := by decide +kernel

end

end PrimeFactorUnimodality.Tests
