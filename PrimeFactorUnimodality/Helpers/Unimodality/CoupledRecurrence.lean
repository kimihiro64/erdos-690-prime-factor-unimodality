import Mathlib.Tactic.Linarith

set_option autoImplicit false

/-!
# Monotonicity propagation for coupled Bernoulli recurrences

This is the abstract induction behind Cambie's positive cases.  Once the
lower-degree coefficient is decreasing and lies below the next coefficient,
the convex recurrence preserves that ordering and makes the next coefficient
decrease forever.
-/

namespace PrimeFactorUnimodality

theorem coupled_recurrence_tail
    (lower current coefficient : Nat → Rat) (start : Nat)
    (hCoefficient : ∀ i, 0 ≤ coefficient i ∧ coefficient i ≤ 1)
    (hRecurrence : ∀ i,
      current (i + 1) = coefficient i * current i +
        (1 - coefficient i) * lower i)
    (hLower : ∀ i, start ≤ i → lower (i + 1) ≤ lower i)
    (hBase : lower start ≤ current start) :
    (∀ i, start ≤ i → lower i ≤ current i) ∧
      (∀ i, start ≤ i → current (i + 1) ≤ current i) := by
  have hInvariant : ∀ offset : Nat,
      lower (start + offset) ≤ current (start + offset) := by
    intro offset
    induction offset with
    | zero => simpa using hBase
    | succ offset ih =>
        have hLowerStep := hLower (start + offset) (by omega)
        have hCoeff := hCoefficient (start + offset)
        have hRec := hRecurrence (start + offset)
        have hCurrentLower :
            lower (start + offset) ≤ current (start + offset + 1) := by
          rw [hRec]
          nlinarith [mul_nonneg hCoeff.1 (sub_nonneg.mpr ih)]
        simpa [Nat.add_assoc] using hLowerStep.trans hCurrentLower
  constructor
  · intro i hi
    obtain ⟨offset, rfl⟩ := Nat.exists_eq_add_of_le hi
    exact hInvariant offset
  · intro i hi
    obtain ⟨offset, rfl⟩ := Nat.exists_eq_add_of_le hi
    have hInv := hInvariant offset
    have hCoeff := hCoefficient (start + offset)
    rw [hRecurrence]
    nlinarith [mul_nonneg (sub_nonneg.mpr hCoeff.2)
      (sub_nonneg.mpr hInv)]

end PrimeFactorUnimodality
