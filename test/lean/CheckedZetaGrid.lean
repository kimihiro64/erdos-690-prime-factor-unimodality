import PrimeFactorUnimodality.Helpers.Analytic.CheckedZetaGrid

/-! # Rational checks and exact interface regressions -/

set_option autoImplicit false

namespace PrimeFactorUnimodality.Tests

noncomputable section

open Complex Finset Fourier ZMod

example (r : RationalGridRows) (d : ZetaGroupedBlock)
    (hd : (r.attach d).shared.Valid) (order : ℕ)
    (h : r.check d.degree order = true) : (r.attach d).Valid := by
  exact PrimeFactorUnimodality.RationalGridRows.valid_of_check r d hd order h

example (r : RationalGridRows) (d : ZetaGroupedBlock)
    (hd : (r.attach d).shared.Valid) (order : ℕ) (h : r.check d.degree order = true)
    (p : ZetaGridPoint) (hp : p.Valid (r.attach d)) :
    ‖riemannZeta ((1 / 2 : ℂ) + p.height (r.attach d) * I) - p.value (r.attach d)‖ ≤
      p.error (r.attach d) := by
  exact PrimeFactorUnimodality.RationalGridRows.norm_zeta_sub_value_le r d hd order h p hp

def zeroTwiddles : RationalTwiddles :=
  ⟨fun n => Vector.replicate (2 ^ (n + 1)) ⟨0, 0⟩, fun _ => 2⟩

def unitRows : RationalGridRows :=
  ⟨[0], fun _ _ => ⟨1, 0⟩, 1, zeroTwiddles, fun _ =>
    .node (.leaf ⟨1, 0⟩ 0) (.leaf ⟨0, 0⟩ 0) #v[⟨1, 0⟩, ⟨1, 0⟩] 0 0⟩
example : unitRows.check 1 0 = true := by decide +kernel
example : ({unitRows with groups := [0, 0]} : RationalGridRows).check 1 0 = false := by decide +kernel

def checkedBase : ZetaGroupedBlock :=
  ⟨1, 0, 1, 0, 0, {0}, fun _ => 0, fun _ _ => 1, fun _ _ => 0⟩

example : (unitRows.attach checkedBase).Valid := by
  apply unitRows.valid_of_check checkedBase ?_ 0 (by decide +kernel)
  constructor
  · norm_num [unitRows, checkedBase, RationalGridRows.attach]
  · intro n hn
    simp [unitRows, checkedBase, RationalGridRows.attach]
  · intro n hn
    simp [unitRows, checkedBase, RationalGridRows.attach, dirichletFrequency]
  · intro b hb j hj
    have hb' : b = 0 := by simpa [unitRows, checkedBase, RationalGridRows.attach] using hb
    have hj' : j = 0 := by simpa [unitRows, checkedBase, RationalGridRows.attach] using hj
    subst b
    subst j
    norm_num [unitRows, checkedBase, RationalGridRows.attach, expSumMoment,
      ZetaGroupedBlock.center, RationalPoint.toComplex]
    apply Complex.ext <;> norm_num

end

end PrimeFactorUnimodality.Tests
