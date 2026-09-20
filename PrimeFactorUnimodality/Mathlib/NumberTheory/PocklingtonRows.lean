import PrimeFactorUnimodality.Mathlib.NumberTheory.Pocklington

set_option autoImplicit false

namespace PrimeFactorUnimodality

/-! Numeric Pocklington certificates are kept separate from the row consumers.
The generated layer supplies only this data and checks one reusable validity
predicate per row; the theorem below performs the conversion to primality. -/
structure PocklingtonData where
  n : Nat
  F : Nat
  R : Nat
  a : Nat
  factors : List Nat

def PocklingtonData.Valid (d : PocklingtonData) : Prop :=
  1 < d.n ∧
    d.n - 1 = d.F * d.R ∧
    d.F = d.factors.prod ∧
    (∀ p ∈ d.factors, p.Prime) ∧
    0 < d.F ∧
    d.n < d.F ^ 2 ∧
    (d.a : ZMod d.n) ^ (d.n - 1) = 1 ∧
    (∀ q : Nat, q ∈ d.factors →
      IsUnit ((d.a : ZMod d.n) ^ ((d.n - 1) / q) - 1)) ∧
    ¬ d.F - 1 ∣ d.n

theorem PocklingtonData.prime
    (d : PocklingtonData) (h : d.Valid) : d.n.Prime := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors
    d.n d.F d.R d.a d.factors
  · exact h.1
  · exact h.2.1
  · exact h.2.2.1
  · exact h.2.2.2.1
  · exact h.2.2.2.2.1
  · exact h.2.2.2.2.2.1
  · exact h.2.2.2.2.2.2.1
  · exact h.2.2.2.2.2.2.2.1
  · exact h.2.2.2.2.2.2.2.2

def PocklingtonRow.Valid (row : List PocklingtonData) : Prop :=
  ∀ d ∈ row, d.Valid

theorem PocklingtonRow.prime_of_mem
    {row : List PocklingtonData} (hrow : PocklingtonRow.Valid row)
    {d : PocklingtonData} (hd : d ∈ row) : d.n.Prime :=
  d.prime (hrow d hd)

end PrimeFactorUnimodality
