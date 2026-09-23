/-
Copyright (c) 2026 Jonas Whidden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonas Whidden
-/
import PrimeFactorUnimodality.Mathlib.Analysis.Fourier.GroupedGrid
import PrimeFactorUnimodality.Mathlib.Analysis.Fourier.RationalTrace

/-! # Rational sparse input assembly for checked Fourier columns

Both rational coordinates are accumulated in shared arrays. Interpretation
agrees with the exact complex alias array, including every collision.
-/

namespace Fourier

open Complex Finset ZMod

/-- One exact rational coordinate is accumulated with one update per input row. -/
def rationalAliasCoordinate (n : ℕ) (rows : List ℤ) (a : ℤ → ℚ) : Vector ℚ (2 ^ n) :=
  (Vector.replicate (2 ^ n) 0).scatterAdd (rows.map fun b : ℤ =>
    (⟨(b : ZMod (2 ^ n)).val, val_lt _⟩, a b))

/-- The coordinate accumulator has the expected complete finite sum. -/
theorem rationalAliasCoordinate_get (n : ℕ) (rows : List ℤ) (a : ℤ → ℚ)
    (k : ZMod (2 ^ n)) :
    (rationalAliasCoordinate n rows a)[k.val]'(val_lt k) =
      (rows.map (fun b : ℤ => if (b : ZMod (2 ^ n)) = k then a b else 0)).sum := by
  rw [rationalAliasCoordinate, Vector.scatterAdd_get _ _ ⟨k.val, val_lt k⟩]
  simp only [Vector.getElem_replicate, zero_add, List.map_map, Function.comp_def,
    Fin.mk.injEq, (ZMod.val_injective (2 ^ n)).eq_iff]

/-- Two shared coordinate passes prepare one rational complex input array. -/
def rationalAliasVector (n : ℕ) (rows : List ℤ) (a : ℤ → RationalPoint) :
    Vector RationalPoint (2 ^ n) :=
  let re := rationalAliasCoordinate n rows (fun b => (a b).re)
  let im := rationalAliasCoordinate n rows (fun b => (a b).im)
  Vector.ofFn fun k => ⟨re[k.val], im[k.val]⟩

/-- Rational input assembly supplies the exact complex input expected by the existing evaluator. -/
theorem rationalAliasVector_map (n : ℕ) (rows : List ℤ) (hr : rows.Nodup)
    (a : ℤ → RationalPoint) :
    (rationalAliasVector n rows a).map RationalPoint.toComplex =
      aliasVector n rows.toFinset (fun b => (a b).toComplex) := by
  apply Vector.ext
  intro i hi
  have hk : (i : ZMod (2 ^ n)).val = i := by simp [ZMod.val_natCast, Nat.mod_eq_of_lt hi]
  have hre := rationalAliasCoordinate_get n rows (fun b => (a b).re) (i : ZMod (2 ^ n))
  have him := rationalAliasCoordinate_get n rows (fun b => (a b).im) (i : ZMod (2 ^ n))
  have ha := aliasVector_get n rows.toFinset (fun b => (a b).toComplex) (i : ZMod (2 ^ n))
  simp only [hk] at hre him ha
  rw [ha]
  simp only [rationalAliasVector, Vector.getElem_map, Vector.getElem_ofFn]
  apply Complex.ext <;> simp [RationalPoint.toComplex, hre, him, aliasCoefficients,
    Finset.sum_filter, ← List.sum_toFinset _ hr] <;>
    apply sum_congr rfl <;> intro b hb <;> split_ifs <;> simp

end Fourier
