import PrimeFactorUnimodality.Helpers.Arithmetic.PackedStrictBounds

/-! # Signed fixed-point separation and independent packed-chunk composition -/

set_option autoImplicit false

namespace PrimeFactorUnimodality.Tests

def strictBounds : PackedStrictBounds 3 :=
  ⟨4, 1 + 256 * 2, 2 + 256 * 3 + 65536, 10, -2⟩

example : strictBounds.check = true := by decide +kernel
example : ({strictBounds with denominator := 0} : PackedStrictBounds 3).check = false :=
  by decide +kernel
example : ({strictBounds with upper := strictBounds.lower} : PackedStrictBounds 3).check = false :=
  by decide +kernel
example : strictBounds.lo 0 = -19 / 10 := by decide +kernel
example : strictBounds.hi 0 = -18 / 10 := by decide +kernel
example (i : Fin 3) : strictBounds.lo i < strictBounds.hi i :=
  PackedStrictBounds.lt_of_check (by decide +kernel) i

example {n : ℕ} {p : PackedStrictBounds n} {a b : Fin n → ℚ}
    (hp : p.Encloses a b) (h : p.check = true) (i : Fin n) : a i < b i :=
  PackedStrictBounds.lt_of_encloses_check hp h i

example (i : Fin 6) :
    Fin.addCases (motive := fun _ => ℚ) strictBounds.lo strictBounds.lo i <
      Fin.addCases (motive := fun _ => ℚ) strictBounds.hi strictBounds.hi i :=
  PackedStrictBounds.lt_append (p := strictBounds) (q := strictBounds)
    (by decide +kernel) (by decide +kernel) i

end PrimeFactorUnimodality.Tests
