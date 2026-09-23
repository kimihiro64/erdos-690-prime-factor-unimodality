/-
Copyright (c) 2026 Jonas Whidden.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonas Whidden
-/
import PrimeFactorUnimodality.Helpers.Arithmetic.PartialSieveRows
import PrimeFactorUnimodality.Mathlib.NumberTheory.PrimeCountingMeissel

/-! # Meissel certificates from checked partial-sieve and quotient rows

The generator supplies all partial sums. Each quotient contributes one local
addition, and a single induction proves the full sum. The mathematical
prime-count inputs must already be certified; no external table is an oracle.
-/

namespace PrimeFactorUnimodality

open Finset

/-- One term of the correction sum with its incoming subtotal. -/
structure MeisselQuotientRow where
  count : ℕ
  subtotal : ℕ

/-- The local check accounts for the exact index-dependent correction. -/
def checkMeisselQuotientRow (rows : ℕ → MeisselQuotientRow) (i : ℕ) : Bool :=
  decide ((rows (i + 1)).subtotal = (rows i).subtotal + ((rows i).count - i + 1))

/-- Adjacent checked rows determine the entire correction sum, without recomputing it. -/
theorem meisselQuotientRows_sum {rows : ℕ → MeisselQuotientRow} {a b : ℕ}
    (hab : a ≤ b) (ha : (rows a).subtotal = 0)
    (hcheck : ∀ i ∈ Ico a b, checkMeisselQuotientRow rows i = true) :
    (∑ i ∈ Ico a b, ((rows i).count - i + 1)) = (rows b).subtotal := by
  induction b, hab using Nat.le_induction with
  | base => simpa using ha.symm
  | succ b hab ih =>
    have hsmall : ∀ i ∈ Ico a b, checkMeisselQuotientRow rows i = true := by
      intro i hi
      exact hcheck i (mem_Ico.mpr ⟨(mem_Ico.mp hi).1, by have := (mem_Ico.mp hi).2; omega⟩)
    have hlast := hcheck b (mem_Ico.mpr ⟨hab, by omega⟩)
    simp only [checkMeisselQuotientRow, decide_eq_true_eq] at hlast
    rw [sum_Ico_succ_top hab, ih hsmall]
    exact hlast.symm

/-- Scalar guard for one Meissel endpoint; only the final excluded prime needs a square check. -/
def checkMeisselEndpoint (p : ℕ → ℕ) (n a b phi total count : ℕ) : Bool :=
  decide (a ≤ b ∧ 1 ≤ n ∧ p b - 1 ≤ n ∧ n < p b ^ 2 ∧ n < p a ^ 3 ∧
    (a < b → p (b - 1) ^ 2 ≤ n) ∧ count + total + 1 = phi + b)

/-- A complete small prime table, one checked sieve claim, and local quotient rows give `π(n)`. -/
theorem primeCounting_eq_of_meissel_rows {p : ℕ → ℕ} {n a b phi count : ℕ}
    {rows : ℕ → MeisselQuotientRow}
    (hp : ∀ i ≤ b, p i = Nat.nth Nat.Prime i)
    (hphi : (PartialSieveClaim.mk a n phi).Valid p)
    (hcounts : ∀ i ∈ Ico a b, Nat.primeCounting (n / p i) = (rows i).count)
    (hstart : (rows a).subtotal = 0)
    (hsteps : ∀ i ∈ Ico a b, checkMeisselQuotientRow rows i = true)
    (hcheck : checkMeisselEndpoint p n a b phi (rows b).subtotal count = true) :
    Nat.primeCounting n = count := by
  simp only [checkMeisselEndpoint, decide_eq_true_eq] at hcheck
  obtain ⟨hab, hn, hb, hsq, hcube, hsquares, hresult⟩ := hcheck
  have hcanonical : Nat.sievePhi (Nat.nth Nat.Prime) a n = phi := by
    rw [← Nat.sievePhi_congr (fun i hi => hp i (by omega)) n]
    exact hphi
  rw [hp b le_rfl] at hb hsq
  rw [hp a hab] at hcube
  have hsmall : ∀ i ∈ Ico a b, Nat.nth Nat.Prime i ^ 2 ≤ n := by
    intro i hi
    obtain ⟨hai, hib⟩ := mem_Ico.mp hi
    have hs := hsquares (by omega)
    rw [hp (b - 1) (by omega)] at hs
    exact (Nat.pow_le_pow_left
      (Nat.nth_monotone Nat.infinite_setOfPred_prime (by omega : i ≤ b - 1)) 2).trans hs
  have h := Nat.primeCounting_meissel hab hn hb hsq hcube hsmall
  rw [hcanonical] at h
  have hterms : (∑ i ∈ Ico a b, (Nat.primeCounting (n / Nat.nth Nat.Prime i) - i + 1)) =
      ∑ i ∈ Ico a b, ((rows i).count - i + 1) := by
    apply sum_congr rfl
    intro i hi
    have he := hcounts i hi
    rw [hp i (by have := (mem_Ico.mp hi).2; omega)] at he
    rw [he]
  rw [hterms, meisselQuotientRows_sum hab hstart hsteps] at h
  omega

end PrimeFactorUnimodality
