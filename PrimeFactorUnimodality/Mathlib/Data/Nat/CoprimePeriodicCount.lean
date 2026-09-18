/-
Copyright (c) 2026 Jonas Whidden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonas Whidden
-/
import Mathlib.Data.ZMod.Basic
import PrimeFactorUnimodality.Mathlib.Data.Nat.Periodic

set_option autoImplicit false

namespace Nat

open Function
open scoped Count

def countSubtypeFinEquiv (p : ℕ → Prop) (n : ℕ) :
    {k : ℕ // k < n ∧ p k} ≃ {i : Fin n // p i.val} where
  toFun k := ⟨⟨k.val, k.prop.1⟩, k.prop.2⟩
  invFun i := ⟨i.val.val, i.val.isLt, i.prop⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem count_eq_card_fin (p : ℕ → Prop) [DecidablePred p] (n : ℕ) :
    Nat.count p n = Fintype.card {i : Fin n // p i.val} := by
  rw [Nat.count_eq_card_fintype]
  exact Fintype.card_congr (countSubtypeFinEquiv p n)

theorem count_and_partition (p q : ℕ → Prop) [DecidablePred p]
    [DecidablePred q] (n : ℕ) :
    Nat.count (fun x => p x ∧ q x) n +
        Nat.count (fun x => p x ∧ ¬ q x) n = Nat.count p n := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Nat.count_succ, Nat.count_succ, Nat.count_succ]
      by_cases hp : p n <;> by_cases hq : q n <;> simp [hp, hq] <;> omega

theorem count_congr_iff (p q : ℕ → Prop) [DecidablePred p]
    [DecidablePred q] (h : ∀ n, p n ↔ q n) (bound : ℕ) :
    Nat.count p bound = Nat.count q bound := by
  induction bound with
  | zero => simp
  | succ n ih =>
      rw [Nat.count_succ, Nat.count_succ, ih]
      simp only [h n]

theorem count_or_of_disjoint (p q : ℕ → Prop) [DecidablePred p]
    [DecidablePred q] (hdisjoint : ∀ n, ¬ (p n ∧ q n)) (n : ℕ) :
    Nat.count (fun x => p x ∨ q x) n = Nat.count p n + Nat.count q n := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Nat.count_succ, Nat.count_succ, Nat.count_succ]
      by_cases hp : p n <;> by_cases hq : q n
      · exact (hdisjoint n ⟨hp, hq⟩).elim
      · simp [hp, hq, ih]
        omega
      · simp [hp, hq, ih]
        omega
      · simp [hp, hq, ih]

/-- The finite Chinese-remainder coordinate equivalence.  Its two coordinates
are represented by least nonnegative residues, so it can be used directly in
finite cardinality arguments over `Nat.count`. -/
def finCrtEquiv {a q : ℕ} [NeZero a] [NeZero q] (h : a.Coprime q) :
    Fin (a * q) ≃ Fin a × Fin q :=
  (ZMod.finEquiv (a * q)).toEquiv.trans
      ((ZMod.chineseRemainder h).toEquiv.trans
      ((ZMod.finEquiv a).symm.toEquiv.prodCongr (ZMod.finEquiv q).symm.toEquiv))

theorem card_finCrtEquiv {a q : ℕ} [NeZero a] [NeZero q]
    (h : a.Coprime q) :
    Fintype.card (Fin (a * q)) = Fintype.card (Fin a × Fin q) :=
  Fintype.card_congr (finCrtEquiv h)

theorem finCrtEquiv_snd_val {a q : ℕ} [NeZero a] [NeZero q]
    (h : a.Coprime q) (n : Fin (a * q)) :
    (finCrtEquiv h n).2.val = n.val % q := by
  cases a with
  | zero => exact (NeZero.ne 0 rfl).elim
  | succ a =>
      cases q with
      | zero => exact (NeZero.ne 0 rfl).elim
      | succ q =>
          change ((n.val : ZMod (q + 1)).val) = n.val % (q + 1)
          exact ZMod.val_natCast (q + 1) n.val

theorem finCrtEquiv_fst_val {a q : ℕ} [NeZero a] [NeZero q]
    (h : a.Coprime q) (n : Fin (a * q)) :
    (finCrtEquiv h n).1.val = n.val % a := by
  cases a with
  | zero => exact (NeZero.ne 0 rfl).elim
  | succ a =>
      cases q with
      | zero => exact (NeZero.ne 0 rfl).elim
      | succ q =>
          change ((n.val : ZMod (a + 1)).val) = n.val % (a + 1)
          exact ZMod.val_natCast (a + 1) n.val

theorem finCrtEquiv_fst_pred_iff {p : ℕ → Prop} {a q : ℕ}
    [NeZero a] [NeZero q] (hp : Periodic p a) (h : a.Coprime q)
    (n : Fin (a * q)) :
    p n.val ↔ p (finCrtEquiv h n).1.val := by
  rw [finCrtEquiv_fst_val h n, hp.map_mod_nat]

theorem finCrtEquiv_snd_eq_zero_iff {a q : ℕ} [NeZero a] [NeZero q]
    (h : a.Coprime q) (n : Fin (a * q)) :
    (finCrtEquiv h n).2 = 0 ↔ q ∣ n.val := by
  rw [Fin.ext_iff, finCrtEquiv_snd_val h n]
  simp [Nat.dvd_iff_mod_eq_zero]

def prodZeroSubtypeEquiv (p : ℕ → Prop) (a q : ℕ) [NeZero q] :
    {x : Fin a × Fin q // p x.1.val ∧ x.2 = 0} ≃
      {i : Fin a // p i.val} where
  toFun x := ⟨x.val.1, x.prop.1⟩
  invFun i := ⟨(i.val, 0), i.prop, rfl⟩
  left_inv x := by
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · exact x.prop.2.symm
  right_inv _ := rfl

def finCrtDvdSubtypeEquiv {p : ℕ → Prop} {a q : ℕ}
    [NeZero a] [NeZero q] (hp : Periodic p a) (h : a.Coprime q) :
    {n : Fin (a * q) // p n.val ∧ q ∣ n.val} ≃
      {i : Fin a // p i.val} :=
  ((finCrtEquiv h).subtypeEquiv fun n =>
      and_congr (finCrtEquiv_fst_pred_iff hp h n)
        (finCrtEquiv_snd_eq_zero_iff h n).symm).trans
    (prodZeroSubtypeEquiv p a q)

theorem count_and_dvd_mul {p : ℕ → Prop} [DecidablePred p]
    {a q : ℕ} (ha : 0 < a) (hq : 0 < q) (hp : Periodic p a)
    (hcoprime : a.Coprime q) :
    Nat.count (fun n => p n ∧ q ∣ n) (a * q) = Nat.count p a := by
  let _ : NeZero a := ⟨ha.ne'⟩
  let _ : NeZero q := ⟨hq.ne'⟩
  rw [count_eq_card_fin, count_eq_card_fin]
  exact Fintype.card_congr (finCrtDvdSubtypeEquiv hp hcoprime)

/-!
# Periodic counts over a commuted product

This is the elementary total-count component of the finite CRT argument.  The
coprime residue refinement belongs in a later theorem; keeping this fact
separate makes its assumptions and reuse explicit.
-/

theorem count_mul_period_commuted {p : ℕ → Prop} [DecidablePred p]
    {a q : ℕ} (hp : Periodic p a) (_q_pos : 0 < q) :
    Nat.count p (a * q) = q * Nat.count p a := by
  rw [Nat.mul_comm]
  exact Nat.count_mul_period hp q

theorem count_and_not_dvd_mul {p : ℕ → Prop} [DecidablePred p]
    {a q : ℕ} (ha : 0 < a) (hq : 0 < q) (hp : Periodic p a)
    (hcoprime : a.Coprime q) :
    Nat.count (fun n => p n ∧ ¬ q ∣ n) (a * q) =
      (q - 1) * Nat.count p a := by
  have hpartition := count_and_partition p (fun n => q ∣ n) (a * q)
  rw [count_and_dvd_mul ha hq hp hcoprime,
    count_mul_period_commuted hp hq] at hpartition
  have hqeq : q = (q - 1) + 1 := by omega
  have htotal : q * Nat.count p a =
      (q - 1) * Nat.count p a + Nat.count p a := by
    calc
      q * Nat.count p a = ((q - 1) + 1) * Nat.count p a :=
        congrArg (fun t => t * Nat.count p a) hqeq
      _ = (q - 1) * Nat.count p a + Nat.count p a := by
        rw [Nat.add_mul, one_mul]
  rw [htotal] at hpartition
  apply Nat.add_left_cancel (n := Nat.count p a)
  calc
    Nat.count p a + Nat.count (fun n => p n ∧ ¬ q ∣ n) (a * q) =
        (q - 1) * Nat.count p a + Nat.count p a := hpartition
    _ = Nat.count p a + (q - 1) * Nat.count p a := by ac_rfl

theorem count_eq_mod_add_div_mul_commuted {p : ℕ → Prop} [DecidablePred p]
    {a q : ℕ} (hp : Periodic p a) (_q_pos : 0 < q) :
    Nat.count p (a * q) =
      Nat.count p ((a * q) % a) + ((a * q) / a) * Nat.count p a := by
  exact Nat.count_eq_mod_add_div_mul hp (a * q)

end Nat
