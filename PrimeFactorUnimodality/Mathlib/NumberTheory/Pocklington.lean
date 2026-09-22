/-
Copyright (c) 2026 Jonas Whidden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonas Whidden
-/
module

public import Mathlib.FieldTheory.Finite.Basic
public import PrimeFactorUnimodality.Mathlib.NumberTheory.PrimalityCongruence

/-!
# A proof-producing partial-factorization Pocklington criterion

This file supplies the ordinary `N - 1` companion to the quadratic `N + 1`
criterion in `BLSPrimality`. Computed residues remain in separate certificate
modules.
-/

@[expose] public section

set_option linter.style.haveILetI false in
/-- A partial-factorization form of Pocklington's primality criterion.

Here `F` is the known factored part of `n - 1`. The proper-power unit
hypotheses are the certificate-friendly form of the usual coprimality
conditions; the main power identity itself implies that the base is a unit. -/
theorem Nat.prime_of_pocklington_factor (n F R a : ℕ)
    (hn : 1 < n)
    (hfactor : n - 1 = F * R)
    (hFpos : 0 < F)
    (hlarge : n < F ^ 2)
    (hmain : (a : ZMod n) ^ (n - 1) = 1)
    (hproper : ∀ q : ℕ, q.Prime → q ∣ F →
      IsUnit ((a : ZMod n) ^ ((n - 1) / q) - 1))
    (hexclude : ¬ F - 1 ∣ n) :
    n.Prime := by
  have hExponent : n - 1 ≠ 0 := by omega
  have hbase : IsUnit (a : ZMod n) :=
    IsUnit.of_pow_eq_one hmain hExponent
  apply Nat.prime_of_large_factor_dvd_sub_or_add hn hlarge _ hexclude
  intro p hp hpn
  letI : Fact p.Prime := ⟨hp⟩
  let f := ZMod.castHom hpn (ZMod p)
  let ap : ZMod p := f (a : ZMod n)
  have hap : IsUnit ap := hbase.map f
  let z : (ZMod p)ˣ := hap.unit
  let gamma := z ^ R
  have hzMain : z ^ (n - 1) = 1 := by
    apply Units.ext
    change ap ^ (n - 1) = 1
    change (f (a : ZMod n)) ^ (n - 1) = 1
    rw [← map_pow, hmain, map_one]
  have hgammaF : gamma ^ F = 1 := by
    dsimp [gamma]
    rw [← pow_mul, mul_comm R F, ← hfactor]
    exact hzMain
  have hgammaProper : ∀ q : ℕ, q.Prime → q ∣ F →
      gamma ^ (F / q) ≠ 1 := by
    intro q hqPrime hqF hgamma
    have huP : IsUnit (ap ^ ((n - 1) / q) - 1) := by
      have hm := (hproper q hqPrime hqF).map f
      change IsUnit (f ((a : ZMod n) ^ ((n - 1) / q) - 1)) at hm
      simpa only [map_sub, map_pow, map_one] using hm
    have hzNe : z ^ ((n - 1) / q) ≠ 1 := by
      intro hzOne
      have heq : ap ^ ((n - 1) / q) = 1 :=
        congrArg ((↑·) : (ZMod p)ˣ → ZMod p) hzOne
      exact huP.ne_zero (sub_eq_zero.mpr heq)
    apply hzNe
    dsimp [gamma] at hgamma
    rw [← pow_mul] at hgamma
    have hexp : R * (F / q) = (n - 1) / q := by
      calc
        R * (F / q) = R * F / q := (Nat.mul_div_assoc R hqF).symm
        _ = (F * R) / q := by rw [mul_comm R F]
        _ = (n - 1) / q := by rw [hfactor]
    rwa [hexp] at hgamma
  have horder : orderOf gamma = F :=
    orderOf_eq_of_pow_and_pow_div_prime hFpos hgammaF hgammaProper
  left
  have hzFermat : z ^ (p - 1) = 1 := by
    apply Units.ext
    change ap ^ (p - 1) = 1
    exact ZMod.pow_card_sub_one_eq_one hap.ne_zero
  have hgammaPow : gamma ^ (p - 1) = 1 := by
    dsimp [gamma]
    rw [← pow_mul, mul_comm R (p - 1), pow_mul, hzFermat, one_pow]
  have hdvd := orderOf_dvd_of_pow_eq_one hgammaPow
  rwa [horder] at hdvd

theorem Nat.prime_of_pocklington_factor_of_prime_factors
    (n F R a : ℕ) (factors : List ℕ)
    (hn : 1 < n)
    (hfactor : n - 1 = F * R)
    (hF : F = factors.prod)
    (hFactorsPrime : ∀ p ∈ factors, p.Prime)
    (hFpos : 0 < F)
    (hlarge : n < F ^ 2)
    (hmain : (a : ZMod n) ^ (n - 1) = 1)
    (hproper : ∀ q : ℕ, q ∈ factors →
      IsUnit ((a : ZMod n) ^ ((n - 1) / q) - 1))
    (hexclude : ¬ F - 1 ∣ n) :
    n.Prime := by
  apply Nat.prime_of_pocklington_factor n F R a hn hfactor hFpos hlarge hmain
  · intro q hq hqF
    apply hproper q
    have hqProd : q ∣ factors.prod := by
      rw [← hF]
      exact hqF
    have prime_mem : ∀ (xs : List ℕ),
        (∀ p ∈ xs, p.Prime) → q ∣ xs.prod → q ∈ xs := by
      intro xs
      induction xs with
      | nil =>
          intro _ h
          have hq2 := hq.two_le
          have hqne : q ≠ 1 := by omega
          have hq1 : q = 1 := by simpa using h
          exact (hqne hq1).elim
      | cons p xs ih =>
          intro hpr hprod
          simp only [List.prod_cons] at hprod
          rcases hq.dvd_mul.mp hprod with hqp | hqrest
          · have hp : p.Prime := hpr p (by simp)
            rcases (Nat.dvd_prime hp).mp hqp with hq1 | hqp
            · have hq2 := hq.two_le
              omega
            · subst p
              simp
          · exact List.mem_cons_of_mem p (ih (by
              intro r hr
              exact hpr r (by simp [hr])) hqrest)
    exact prime_mem factors hFactorsPrime hqProd
  · exact hexclude
