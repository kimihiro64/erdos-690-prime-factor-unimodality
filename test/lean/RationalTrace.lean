import PrimeFactorUnimodality.Mathlib.Analysis.Fourier.RationalTrace

/-! # Rational checks and exact interface regressions -/

set_option autoImplicit false

namespace PrimeFactorUnimodality.Tests

noncomputable section

open Complex Finset Fourier ZMod

example {N : ℕ} (f : Fin N → Bool) :
    allIndices f = true ↔ ∀ k, f k = true := by
  exact Fourier.allIndices_eq_true f

example {p : RationalTwiddles} {n m : ℕ}
    (hp : p.Valid n) (hm : m ≤ n) : p.Valid m := by
  exact Fourier.RationalTwiddles.Valid.mono hp hm

example (p : RationalTwiddles) {n : ℕ}
    (t : RationalTrace n) : (t.semantic p).values = t.values.map RationalPoint.toComplex := by
  exact Fourier.RationalTrace.values_semantic p t

example {α β : Type*} (n : ℕ) (f : α → β) (a : Vector α (2 ^ (n + 1))) :
    evenSamples n (a.map f) = (evenSamples n a).map f := by
  exact Fourier.evenSamples_map n f a

example {α β : Type*} (n : ℕ) (f : α → β) (a : Vector α (2 ^ (n + 1))) :
    oddSamples n (a.map f) = (oddSamples n a).map f := by
  exact Fourier.oddSamples_map n f a

example {p : RationalTwiddles} {n : ℕ} (hp : p.Valid n)
    (t : RationalTrace n) (a : Vector RationalPoint (2 ^ n)) (h : t.check p a = true) :
    (t.semantic p).Valid (radixRoot n) (a.map RationalPoint.toComplex) := by
  exact Fourier.RationalTrace.valid_of_check hp t a h

def zeroTwiddles : RationalTwiddles :=
  ⟨fun n => Vector.replicate (2 ^ (n + 1)) ⟨0, 0⟩, fun _ => 2⟩

def rationalPair : RationalTrace 1 :=
  .node (.leaf ⟨1, 0⟩ 0) (.leaf ⟨3, 0⟩ 0) #v[⟨1, 0⟩, ⟨1, 0⟩] 0 3
example : rationalPair.check zeroTwiddles #v[⟨1, 0⟩, ⟨3, 0⟩] = true := by decide +kernel
example : rationalPair.check zeroTwiddles #v[⟨1, 0⟩, ⟨4, 0⟩] = false := by decide +kernel
example : (RationalTrace.leaf ⟨0, 0⟩ (-1)).check zeroTwiddles #v[⟨0, 0⟩] = false := by decide +kernel
example : allIndices (fun _ : Fin 0 => false) = true := by decide +kernel
example : allIndices (fun k : Fin 3 => decide (k.val < 2)) = false := by decide +kernel

end

end PrimeFactorUnimodality.Tests
