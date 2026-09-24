/-
Compatibility facade for the Apache-2.0 PrimeNumberTheoremAnd development.
The original port used revision 47fa48680663df41146704d02a5b092d792bd5b9.
The shared implementation is pinned at f6147e7572ab3abe5428101bc0b13627bcb005df.
-/

module

public import PrimeNumberTheoremAnd.EulerMaclaurin

/-! # One shared Euler--Maclaurin implementation

Mertens and the Dusart digamma development need the same first-order formula.
Re-export the pinned, proved implementation instead of redeclaring its global
names: two independent definitions of `B1` cannot coexist in a Lean environment.
The dependency imports only Mathlib's Abel summation module. This facade keeps
existing import paths and theorem names while permitting both proof chains to
be assembled in one environment.
-/
