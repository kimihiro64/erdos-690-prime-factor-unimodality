/-
Copyright (c) 2026 Jonas Whidden. All rights reserved.
Released under Apache 2.0 license as described in the repository LICENSE.
Standalone MathDB E690 proof. The finite CRT counting lemmas and density
argument are adapted from the verified prime-factor-unimodality library.
-/
import FtpEvalBench.E690
import Mathlib.Algebra.BigOperators.Group.List.Defs
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Nat.GCD.BigOperators
import Mathlib.Data.Nat.Periodic
import Mathlib.Data.Nat.PrimeFin
import Mathlib.Data.ZMod.Basic
import Mathlib.Order.Filter.AtTopBot.Archimedean
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Topology.MetricSpace.Pseudo.Lemmas

/-!
# Standalone negative answer for MathDB E690

For every prime p, a finite periodic CRT count supplies its actual natural
density at k=4. The exact rational valley at primes 13, 17, and 19 rules out
every possible mode. No project module, analytic hypothesis, external oracle,
or large enumeration is imported into this submission.
-/

set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000

namespace Submission

-- ASCII spellings used to keep this standalone source portable.
local infixr:35 " AND " => And
local infixr:30 " OR " => Or
local prefix:40 "NOT " => Not
local infix:50 " DVD " => Dvd.dvd
local infix:50 " IN " => fun x s => Membership.mem s x
local infixl:70 " ANDSET " => Inter.inter
local infixr:25 " IFF " => Iff
local infix:25 " EQUIV " => Equiv
local infixr:35 " PROD " => Prod

namespace Nat

open Function

/-- A periodic predicate has the same number of witnesses in every whole
number of periods. -/
theorem count_mul_period {p : Nat  ->  Prop} [DecidablePred p]
    {a : Nat} (hp : Periodic p a) (q : Nat) :
    Nat.count p (q * a) = q * Nat.count p a := by
  induction q with
  | zero => simp
  | succ q ih =>
      rw [Nat.succ_mul, Nat.count_add, ih, Nat.succ_mul]
      congr 1
      congr 1
      funext k
      exact propext (by
        simpa [Nat.nsmul_eq_mul, add_comm] using hp.nsmul q k)

/-- Split the count of a periodic predicate into complete periods and its
final incomplete period. -/
theorem count_eq_mod_add_div_mul {p : Nat  ->  Prop} [DecidablePred p]
    {a : Nat} (hp : Periodic p a) (n : Nat) :
    Nat.count p n = Nat.count p (n % a) + (n / a) * Nat.count p a := by
  calc
    Nat.count p n = Nat.count p (a * (n / a) + n % a) := by
      congr 1
      simpa [add_comm] using (n.mod_add_div a).symm
    _ = Nat.count p (a * (n / a)) +
        Nat.count (fun k => p (a * (n / a) + k)) (n % a) :=
      Nat.count_add _ _ _
    _ = (n / a) * Nat.count p a + Nat.count p (n % a) := by
      rw [show Nat.count p (a * (n / a)) = (n / a) * Nat.count p a by
        simpa [mul_comm] using Nat.count_mul_period hp (n / a)]
      congr 1
      unfold Nat.count
      apply List.countP_congr
      intro k hk
      have hprop : p (a * (n / a) + k) = p k := by
        simpa only [Nat.nsmul_eq_mul, mul_comm (n / a) a,
          add_comm k (a * (n / a))] using hp.nsmul (n / a) k
      simpa only [decide_eq_true_eq] using hprop.to_iff
    _ = Nat.count p (n % a) + (n / a) * Nat.count p a := add_comm _ _

end Nat

namespace Nat

open Function
open scoped Count

def countSubtypeFinEquiv (p : Nat  ->  Prop) (n : Nat) :
    {k : Nat // k < n  AND  p k}  EQUIV  {i : Fin n // p i.val} where
  toFun k := Subtype.mk (Fin.mk k.val k.prop.1) k.prop.2
  invFun i := Subtype.mk i.val.val (And.intro i.val.isLt i.prop)
  left_inv _ := rfl
  right_inv _ := rfl

theorem count_eq_card_fin (p : Nat  ->  Prop) [DecidablePred p] (n : Nat) :
    Nat.count p n = Fintype.card {i : Fin n // p i.val} := by
  rw [Nat.count_eq_card_fintype]
  exact Fintype.card_congr (countSubtypeFinEquiv p n)

theorem count_and_partition (p q : Nat  ->  Prop) [DecidablePred p]
    [DecidablePred q] (n : Nat) :
    Nat.count (fun x => p x  AND  q x) n +
        Nat.count (fun x => p x  AND  NOT  q x) n = Nat.count p n := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Nat.count_succ, Nat.count_succ, Nat.count_succ]
      by_cases hp : p n <;> by_cases hq : q n <;> simp [hp, hq] <;> omega

theorem count_congr_iff (p q : Nat  ->  Prop) [DecidablePred p]
    [DecidablePred q] (h : forall  n, p n  IFF  q n) (bound : Nat) :
    Nat.count p bound = Nat.count q bound := by
  induction bound with
  | zero => simp
  | succ n ih =>
      rw [Nat.count_succ, Nat.count_succ, ih]
      simp only [h n]

theorem count_or_of_disjoint (p q : Nat  ->  Prop) [DecidablePred p]
    [DecidablePred q] (hdisjoint : forall  n, NOT  (p n  AND  q n)) (n : Nat) :
    Nat.count (fun x => p x  OR  q x) n = Nat.count p n + Nat.count q n := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Nat.count_succ, Nat.count_succ, Nat.count_succ]
      by_cases hp : p n <;> by_cases hq : q n
      next =>
        exact (hdisjoint n (And.intro hp hq)).elim
      next =>
        simp [hp, hq, ih]
        omega
      next =>
        simp [hp, hq, ih]
        omega
      next =>
        simp [hp, hq, ih]

/-- The finite Chinese-remainder coordinate equivalence.  Its two coordinates
are represented by least nonnegative residues, so it can be used directly in
finite cardinality arguments over `Nat.count`. -/
def finCrtEquiv {a q : Nat} [NeZero a] [NeZero q] (h : a.Coprime q) :
    Fin (a * q)  EQUIV  Fin a  PROD  Fin q :=
  (ZMod.finEquiv (a * q)).toEquiv.trans
      ((ZMod.chineseRemainder h).toEquiv.trans
      ((ZMod.finEquiv a).symm.toEquiv.prodCongr (ZMod.finEquiv q).symm.toEquiv))

theorem card_finCrtEquiv {a q : Nat} [NeZero a] [NeZero q]
    (h : a.Coprime q) :
    Fintype.card (Fin (a * q)) = Fintype.card (Fin a  PROD  Fin q) :=
  Fintype.card_congr (finCrtEquiv h)

theorem finCrtEquiv_snd_val {a q : Nat} [NeZero a] [NeZero q]
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

theorem finCrtEquiv_fst_val {a q : Nat} [NeZero a] [NeZero q]
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

theorem finCrtEquiv_fst_pred_iff {p : Nat  ->  Prop} {a q : Nat}
    [NeZero a] [NeZero q] (hp : Periodic p a) (h : a.Coprime q)
    (n : Fin (a * q)) :
    p n.val  IFF  p (finCrtEquiv h n).1.val := by
  rw [finCrtEquiv_fst_val h n, hp.map_mod_nat]

theorem finCrtEquiv_snd_eq_zero_iff {a q : Nat} [NeZero a] [NeZero q]
    (h : a.Coprime q) (n : Fin (a * q)) :
    (finCrtEquiv h n).2 = 0  IFF  q  DVD  n.val := by
  rw [Fin.ext_iff, finCrtEquiv_snd_val h n]
  simp [Nat.dvd_iff_mod_eq_zero]

def prodZeroSubtypeEquiv (p : Nat  ->  Prop) (a q : Nat) [NeZero q] :
    {x : Fin a  PROD  Fin q // p x.1.val  AND  x.2 = 0}  EQUIV
      {i : Fin a // p i.val} where
  toFun x := Subtype.mk x.val.1 x.prop.1
  invFun i := Subtype.mk (i.val, 0) (And.intro i.prop rfl)
  left_inv x := by
    apply Subtype.ext
    apply Prod.ext
    next =>
      rfl
    next =>
      exact x.prop.2.symm
  right_inv _ := rfl

def finCrtDvdSubtypeEquiv {p : Nat  ->  Prop} {a q : Nat}
    [NeZero a] [NeZero q] (hp : Periodic p a) (h : a.Coprime q) :
    {n : Fin (a * q) // p n.val  AND  q  DVD  n.val}  EQUIV
      {i : Fin a // p i.val} :=
  ((finCrtEquiv h).subtypeEquiv fun n =>
      and_congr (finCrtEquiv_fst_pred_iff hp h n)
        (finCrtEquiv_snd_eq_zero_iff h n).symm).trans
    (prodZeroSubtypeEquiv p a q)

theorem count_and_dvd_mul {p : Nat  ->  Prop} [DecidablePred p]
    {a q : Nat} (ha : 0 < a) (hq : 0 < q) (hp : Periodic p a)
    (hcoprime : a.Coprime q) :
    Nat.count (fun n => p n  AND  q  DVD  n) (a * q) = Nat.count p a := by
  let _ : NeZero a := (NeZero.mk ha.ne')
  let _ : NeZero q := (NeZero.mk hq.ne')
  rw [count_eq_card_fin, count_eq_card_fin]
  exact Fintype.card_congr (finCrtDvdSubtypeEquiv hp hcoprime)

/-
# Periodic counts over a commuted product

This is the elementary total-count component of the finite CRT argument.  The
coprime residue refinement belongs in a later theorem; keeping this fact
separate makes its assumptions and reuse explicit.
-/

theorem count_mul_period_commuted {p : Nat  ->  Prop} [DecidablePred p]
    {a q : Nat} (hp : Periodic p a) (_q_pos : 0 < q) :
    Nat.count p (a * q) = q * Nat.count p a := by
  rw [Nat.mul_comm]
  exact Nat.count_mul_period hp q

theorem count_and_not_dvd_mul {p : Nat  ->  Prop} [DecidablePred p]
    {a q : Nat} (ha : 0 < a) (hq : 0 < q) (hp : Periodic p a)
    (hcoprime : a.Coprime q) :
    Nat.count (fun n => p n  AND  NOT  q  DVD  n) (a * q) =
      (q - 1) * Nat.count p a := by
  have hpartition := count_and_partition p (fun n => q  DVD  n) (a * q)
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
    Nat.count p a + Nat.count (fun n => p n  AND  NOT  q  DVD  n) (a * q) =
        (q - 1) * Nat.count p a + Nat.count p a := hpartition
    _ = Nat.count p a + (q - 1) * Nat.count p a := by ac_rfl

theorem count_eq_mod_add_div_mul_commuted {p : Nat  ->  Prop} [DecidablePred p]
    {a q : Nat} (hp : Periodic p a) (_q_pos : 0 < q) :
    Nat.count p (a * q) =
      Nat.count p ((a * q) % a) + ((a * q) / a) * Nat.count p a := by
  exact Nat.count_eq_mod_add_div_mul hp (a * q)

end Nat

namespace E690Proof
def primesBelow (p : Nat) : List Nat :=
  ((Finset.range p).filter Nat.Prime).sort (fun a b => a <= b)
def selectionNumerator : List Nat  ->  Nat  ->  Nat
  | [], 0 => 1
  | [], _ + 1 => 0
  | p :: entries, 0 => (p - 1) * selectionNumerator entries 0
  | p :: entries, r + 1 =>
      (p - 1) * selectionNumerator entries (r + 1) +
        selectionNumerator entries r


end E690Proof

open Filter Function
open scoped Topology

namespace E690Proof

/-- A predicate has natural density `d` when its normalized initial-segment
counts converge to `d`. -/
def HasNaturalDensity (predicate : Nat  ->  Prop) [DecidablePred predicate]
    (density : Real) : Prop :=
  Tendsto (fun n => (Nat.count predicate n : Real) / (n : Real)) atTop (nhds  density)

/-- Pointwise equivalent predicates have the same natural-density statement. -/
theorem HasNaturalDensity.congr {predicate predicate' : Nat  ->  Prop}
    [DecidablePred predicate] [DecidablePred predicate'] {density : Real}
    (has_density : HasNaturalDensity predicate density)
    (equivalent : forall  n, predicate n  IFF  predicate' n) :
    HasNaturalDensity predicate' density := by
  unfold HasNaturalDensity at has_density
  unfold HasNaturalDensity
  apply has_density.congr'
  exact .of_forall fun n => by
    change (Nat.count predicate n : Real) / (n : Real) =
      (Nat.count predicate' n : Real) / (n : Real)
    have count_equal : Nat.count predicate n = Nat.count predicate' n := by
      rw [Nat.count_eq_card_filter_range, Nat.count_eq_card_filter_range]
      apply congrArg Finset.card
      ext x
      simp only [Finset.mem_filter, Finset.mem_range]
      exact and_congr Iff.rfl (equivalent x)
    rw [count_equal]

/-- The natural density of a periodic predicate is its proportion in one
positive period. -/
theorem hasNaturalDensity_of_periodic {predicate : Nat  ->  Prop}
    [DecidablePred predicate] {period : Nat} (period_pos : 0 < period)
    (periodic : Periodic predicate period) :
    HasNaturalDensity predicate
      ((Nat.count predicate period : Real) / (period : Real)) := by
  have remainder_tends_to_zero : Tendsto
      (fun n : Nat => (Nat.count predicate (n % period) : Real) / (n : Real))
      atTop (nhds  0) := by
    apply tendsto_bdd_div_atTop_nhds_zero
      (b := (0 : Real)) (B := (period : Real))
    next =>
      exact .of_forall fun n => by positivity
    next =>
      exact .of_forall fun n => by
        change (Nat.count predicate (n % period) : Real)  <=  (period : Real)
        exact_mod_cast (Nat.count_le (p := predicate)).trans
          (Nat.mod_lt n period_pos).le
    next =>
      exact tendsto_natCast_atTop_atTop
  have mod_div_tends_to_zero : Tendsto
      (fun n : Nat => ((n % period : Nat) : Real) / (n : Real)) atTop (nhds  0) := by
    apply tendsto_bdd_div_atTop_nhds_zero
      (b := (0 : Real)) (B := (period : Real))
    next =>
      exact .of_forall fun n => by positivity
    next =>
      exact .of_forall fun n => by
        change ((n % period : Nat) : Real)  <=  (period : Real)
        exact_mod_cast (Nat.mod_lt n period_pos).le
    next =>
      exact tendsto_natCast_atTop_atTop
  have complete_periods_tendsto_density : Tendsto
      (fun n : Nat => ((Nat.count predicate period : Real) / (period : Real)) *
        (1 - ((n % period : Nat) : Real) / (n : Real))) atTop
      (nhds  ((Nat.count predicate period : Real) / (period : Real))) := by
    have constant_density : Tendsto
        (fun _ : Nat => (Nat.count predicate period : Real) / (period : Real))
        atTop (nhds ((Nat.count predicate period : Real) / (period : Real))) :=
      tendsto_const_nhds
    have constant_one : Tendsto (fun _ : Nat => (1 : Real)) atTop (nhds 1) :=
      tendsto_const_nhds
    simpa using constant_density.mul (constant_one.sub mod_div_tends_to_zero)
  unfold HasNaturalDensity
  have combined_limit : Tendsto
      (fun n : Nat => (Nat.count predicate (n % period) : Real) / (n : Real) +
        ((Nat.count predicate period : Real) / (period : Real)) *
          (1 - ((n % period : Nat) : Real) / (n : Real)))
      atTop (nhds ((Nat.count predicate period : Real) / (period : Real))) := by
    simpa using remainder_tends_to_zero.add complete_periods_tendsto_density
  apply combined_limit.congr'
  filter_upwards [eventually_gt_atTop 0] with n n_pos
  have count_decomposition := Nat.count_eq_mod_add_div_mul periodic n
  rw [count_decomposition]
  push_cast
  have division_algorithm :
      (period : Real) * ((n / period : Nat) : Real) +
          ((n % period : Nat) : Real) = (n : Real) := by
    exact_mod_cast (by
      simpa [add_comm] using n.mod_add_div period)
  field_simp [period_pos.ne', n_pos.ne']
  nlinarith

/-- Delete the value at zero from a predicate. -/
def WithoutZero (predicate : Nat  ->  Prop) (n : Nat) : Prop :=
  Not (n = 0)  AND  predicate n

instance instDecidablePredWithoutZero (predicate : Nat  ->  Prop)
    [DecidablePred predicate] : DecidablePred (WithoutZero predicate) :=
  fun n => by
    unfold WithoutZero
    infer_instance

theorem count_withoutZero_succ {predicate : Nat  ->  Prop}
    [DecidablePred predicate] (n : Nat) :
    Nat.count (WithoutZero predicate) (n + 1) + (if predicate 0 then 1 else 0) =
      Nat.count predicate (n + 1) := by
  rw [Nat.count_succ', Nat.count_succ']
  simp [WithoutZero]

/-- Removing the exceptional value at zero does not change natural density. -/
theorem HasNaturalDensity.withoutZero {predicate : Nat  ->  Prop}
    [DecidablePred predicate] {density : Real}
    (has_density : HasNaturalDensity predicate density) :
    HasNaturalDensity (WithoutZero predicate) density := by
  by_cases holds_at_zero : predicate 0
  next =>
    have correction_tends_to_zero : Tendsto
        (fun n : Nat => (1 : Real) / (n : Real)) atTop (nhds  0) :=
      tendsto_bdd_div_atTop_nhds_zero
        (.of_forall fun _ => by positivity)
        (.of_forall fun _ => le_rfl)
        tendsto_natCast_atTop_atTop
    unfold HasNaturalDensity at has_density
    unfold HasNaturalDensity
    have corrected_limit : Tendsto
        (fun n : Nat => (Nat.count predicate n : Real) / (n : Real) -
          (1 : Real) / (n : Real)) atTop (nhds density) := by
      simpa using has_density.sub correction_tends_to_zero
    apply corrected_limit.congr'
    filter_upwards [eventually_gt_atTop 0] with n n_pos
    let hex := Nat.exists_eq_succ_of_ne_zero n_pos.ne'
    let m := hex.choose
    have hm : n = m.succ := hex.choose_spec
    rw [hm, show m.succ = m + 1 by omega]
    have count_identity := count_withoutZero_succ (predicate := predicate) m
    simp only [holds_at_zero, ite_true] at count_identity
    have cast_identity :
        (Nat.count (WithoutZero predicate) (m + 1) : Real) + 1 =
          (Nat.count predicate (m + 1) : Real) := by
      exact_mod_cast count_identity
    rw [<-  cast_identity]
    field_simp
    ring
  next =>
    have predicates_equal : WithoutZero predicate = predicate := by
      funext n
      apply propext
      cases n with
      | zero => simp [WithoutZero, holds_at_zero]
      | succ n => simp [WithoutZero]
    simpa [predicates_equal] using has_density

end E690Proof

namespace E690Proof

/-- The number of entries in a finite list which divide `n`. -/
def selectedDivisorCount (entries : List Nat) (n : Nat) : Nat :=
  (entries.filter fun entry => entry  DVD  n).length

/-- Divisibility by `p`, together with exactly `r` selected divisors from a
finite list. -/
def HasSelectedDivisors (entries : List Nat) (r p n : Nat) : Prop :=
  p  DVD  n  AND  selectedDivisorCount entries n = r

theorem hasSelectedDivisors_cons_zero_iff (q : Nat) (entries : List Nat) (p n : Nat) :
    HasSelectedDivisors (q :: entries) 0 p n  IFF
      NOT  q  DVD  n  AND  HasSelectedDivisors entries 0 p n := by
  by_cases hq : q  DVD  n <;>
    simp [HasSelectedDivisors, selectedDivisorCount, hq]

theorem hasSelectedDivisors_cons_succ_iff
    (q : Nat) (entries : List Nat) (r p n : Nat) :
    HasSelectedDivisors (q :: entries) (r + 1) p n  IFF
      (q  DVD  n  AND  HasSelectedDivisors entries r p n)  OR
        (NOT  q  DVD  n  AND  HasSelectedDivisors entries (r + 1) p n) := by
  by_cases hq : q  DVD  n <;>
    simp [HasSelectedDivisors, selectedDivisorCount, hq]

theorem hasSelectedDivisors_empty_iff (p n : Nat) :
    HasSelectedDivisors [] 0 p n  IFF  p  DVD  n := by
  simp [HasSelectedDivisors, selectedDivisorCount]

instance instDecidablePredHasSelectedDivisors (entries : List Nat) (r p : Nat) :
    DecidablePred (HasSelectedDivisors entries r p) := fun n => by
  unfold HasSelectedDivisors
  infer_instance

theorem count_hasSelectedDivisors_empty (p : Nat) (hp : 0 < p) :
    Nat.count (HasSelectedDivisors [] 0 p) p = 1 := by
  rw [Nat.count_eq_card_filter_range]
  have hfilter : (Finset.range p).filter (HasSelectedDivisors [] 0 p) = {0} := by
    ext n
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_singleton]
    constructor
    next =>
      intro hyp
      have hnlt := hyp.1
      have hnp := hyp.2
      rw [hasSelectedDivisors_empty_iff] at hnp
      exact Nat.eq_zero_of_dvd_of_lt hnp hnlt
    next =>
      intro hn
      subst n
      exact And.intro hp (And.intro (dvd_zero p) rfl)
  rw [hfilter]
  simp

theorem selectedDivisorCount_add_of_dvd (entries : List Nat) {shift : Nat}
    (shift_dvd : forall entry, entry IN entries -> entry  DVD  shift) (n : Nat) :
    selectedDivisorCount entries (n + shift) =
      selectedDivisorCount entries n := by
  unfold selectedDivisorCount
  congr 1
  apply List.filter_congr
  intro entry entry_mem
  simp only [(Nat.dvd_add_iff_left (shift_dvd entry entry_mem)).symm]

theorem selectedDivisorCount_add_prod (entries : List Nat) (n : Nat) :
    selectedDivisorCount entries (n + entries.prod) =
      selectedDivisorCount entries n :=
  selectedDivisorCount_add_of_dvd entries
    (fun _entry entry_mem => List.dvd_prod entry_mem) n

/-- The selected-divisor predicate has period equal to the product of the
candidate divisor and the finite input list. -/
theorem hasSelectedDivisors_periodic (entries : List Nat) (r p : Nat) :
    Periodic (HasSelectedDivisors entries r p) (p * entries.prod) := by
  intro n
  apply propext
  have p_dvd_shift : p  DVD  p * entries.prod := dvd_mul_right p entries.prod
  have count_periodic :
      selectedDivisorCount entries (n + p * entries.prod) =
        selectedDivisorCount entries n := by
    apply selectedDivisorCount_add_of_dvd
    intro entry entry_mem
    exact dvd_mul_of_dvd_right (List.dvd_prod entry_mem) p
  unfold HasSelectedDivisors
  rw [count_periodic]
  exact and_congr (Nat.dvd_add_iff_left p_dvd_shift).symm Iff.rfl

def ValidSelectionEntries (p : Nat) : List Nat  ->  Prop
  | [] => True
  | q :: entries =>
      0 < q  AND  (p * entries.prod).Coprime q  AND  ValidSelectionEntries p entries

theorem validSelectionEntries_prod_pos {p : Nat} (hp : 0 < p) :
    forall  {entries : List Nat}, ValidSelectionEntries p entries  ->  0 < p * entries.prod
  | [], _ => by simpa using hp
  | q :: entries, hvalid => by
      rw [List.prod_cons]
      exact Nat.mul_pos hp (Nat.mul_pos hvalid.1
        (Nat.pos_of_mul_pos_left
          (validSelectionEntries_prod_pos hp hvalid.2.2)))

theorem validSelectionEntries_of_primes (p : Nat) (p_prime : p.Prime) :
    forall  (entries : List Nat),
      (forall q, q IN entries -> q.Prime)  ->  Not (p IN entries)  ->  entries.Nodup  ->
        ValidSelectionEntries p entries
  | [], _, _, _ => trivial
  | q :: entries, all_prime, p_not_mem, nodup => by
      have q_prime : q.Prime := all_prime q (by simp)
      have p_ne_q : Not (p = q) := by
        intro hpq
        apply p_not_mem
        simp [hpq]
      have prod_coprime_q : entries.prod.Coprime q := by
        rw [Nat.coprime_list_prod_left_iff]
        intro a ha
        apply (Nat.coprime_primes (all_prime a (by simp [ha])) q_prime).2
        intro haq
        subst a
        exact (List.nodup_cons.mp nodup).1 ha
      refine And.intro q_prime.pos (And.intro ?_ ?_)
      next =>
        rw [Nat.coprime_mul_iff_left]
        exact And.intro ((Nat.coprime_primes p_prime q_prime).2 p_ne_q) prod_coprime_q
      next =>
        exact validSelectionEntries_of_primes p p_prime entries
          (fun a ha => all_prime a (by simp [ha]))
          (fun hp_mem => p_not_mem (by simp [hp_mem]))
          (List.nodup_cons.mp nodup).2

theorem validSelectionEntries_primesBelow {p : Nat} (p_prime : p.Prime) :
    ValidSelectionEntries p (primesBelow p) := by
  apply validSelectionEntries_of_primes p p_prime
  next =>
    intro q hq
    exact (by simpa [primesBelow] using hq : q < p  AND  q.Prime).2
  next =>
    simp [primesBelow]
  next =>
    exact Finset.sort_nodup _ _

theorem count_hasSelectedDivisors_eq_selectionNumerator
    (p : Nat) (hp : 0 < p) :
    forall  (entries : List Nat), ValidSelectionEntries p entries  ->  forall  r : Nat,
      Nat.count (HasSelectedDivisors entries r p) (p * entries.prod) =
        selectionNumerator entries r
  | [], _, r => by
      cases r with
      | zero => simpa [selectionNumerator] using count_hasSelectedDivisors_empty p hp
      | succ r =>
          apply Nat.count_of_forall_not
          intro n hn
          simp [HasSelectedDivisors, selectedDivisorCount]
  | q :: entries, hvalid, r => by
      have hperiodPos := validSelectionEntries_prod_pos hp hvalid.2.2
      have hbound : p * (q :: entries).prod = (p * entries.prod) * q := by
        simp only [List.prod_cons]
        ac_rfl
      cases r with
      | zero =>
          calc
            Nat.count (HasSelectedDivisors (q :: entries) 0 p)
                (p * (q :: entries).prod) =
                Nat.count (fun n =>
                  HasSelectedDivisors entries 0 p n  AND  NOT  q  DVD  n)
                  ((p * entries.prod) * q) := by
              rw [hbound]
              apply Nat.count_congr_iff
              intro n
              rw [hasSelectedDivisors_cons_zero_iff]
              tauto
            _ = (q - 1) * Nat.count (HasSelectedDivisors entries 0 p)
                  (p * entries.prod) :=
              Nat.count_and_not_dvd_mul hperiodPos hvalid.1
                (hasSelectedDivisors_periodic entries 0 p) hvalid.2.1
            _ = selectionNumerator (q :: entries) 0 := by
              rw [count_hasSelectedDivisors_eq_selectionNumerator p hp entries
                hvalid.2.2 0]
              rfl
      | succ r =>
          let left : Nat  ->  Prop := fun n =>
            HasSelectedDivisors entries r p n  AND  q  DVD  n
          let right : Nat  ->  Prop := fun n =>
            HasSelectedDivisors entries (r + 1) p n  AND  NOT  q  DVD  n
          calc
            Nat.count (HasSelectedDivisors (q :: entries) (r + 1) p)
                (p * (q :: entries).prod) =
                Nat.count (fun n => left n  OR  right n)
                  ((p * entries.prod) * q) := by
              rw [hbound]
              apply Nat.count_congr_iff
              intro n
              simpa [left, right, and_comm] using
                hasSelectedDivisors_cons_succ_iff q entries r p n
            _ = Nat.count left ((p * entries.prod) * q) +
                Nat.count right ((p * entries.prod) * q) := by
              apply Nat.count_or_of_disjoint
              intro n hyp
              exact hyp.2.2 hyp.1.2
            _ = Nat.count (HasSelectedDivisors entries r p) (p * entries.prod) +
                (q - 1) * Nat.count
                  (HasSelectedDivisors entries (r + 1) p) (p * entries.prod) := by
              rw [show Nat.count left ((p * entries.prod) * q) =
                    Nat.count (HasSelectedDivisors entries r p) (p * entries.prod) by
                  exact Nat.count_and_dvd_mul hperiodPos hvalid.1
                    (hasSelectedDivisors_periodic entries r p) hvalid.2.1,
                show Nat.count right ((p * entries.prod) * q) =
                    (q - 1) * Nat.count
                      (HasSelectedDivisors entries (r + 1) p) (p * entries.prod) by
                  exact Nat.count_and_not_dvd_mul hperiodPos hvalid.1
                    (hasSelectedDivisors_periodic entries (r + 1) p) hvalid.2.1]
            _ = selectionNumerator (q :: entries) (r + 1) := by
              rw [count_hasSelectedDivisors_eq_selectionNumerator p hp entries
                  hvalid.2.2 r,
                count_hasSelectedDivisors_eq_selectionNumerator p hp entries
                  hvalid.2.2 (r + 1)]
              simp only [selectionNumerator]
              omega


theorem selectedDivisorCount_primesBelow (p n : Nat) (n_ne_zero : Not (n = 0)) :
    selectedDivisorCount (primesBelow p) n =
      (n.primeFactors.filter fun q => q < p).card := by
  let candidates := (Finset.range p).filter Nat.Prime
  change (List.filter (fun entry => decide (entry  DVD  n))
      (candidates.sort fun a b => a  <=  b)).length = _
  rw [<-  List.toFinset_card_of_nodup
    ((Finset.sort_nodup candidates (fun a b => a  <=  b)).filter _)]
  congr 1
  ext q
  simp [candidates, Nat.mem_primeFactors, n_ne_zero, and_left_comm, and_assoc]
  tauto


end E690Proof

namespace E690Proof
open Filter
open scoped Topology

/-- Predicate counts use the same initial segments as MathDB's set density. -/
theorem HasNaturalDensity.toSet {predicate : Nat -> Prop}
    [DecidablePred predicate] {density : Real}
    (h : HasNaturalDensity predicate density) :
    Set.HasDensity {n | predicate n} density := by
  have counts (n : Nat) :
      ({x : Nat | predicate x} ANDSET Set.Iio n).ncard =
        Nat.count predicate n := by
    rw [Nat.count_eq_card_filter_range]
    have hset : ({x : Nat | predicate x} ANDSET Set.Iio n) =
        (((Finset.range n).filter predicate : Finset Nat) : Set Nat) := by
      ext x
      change Iff (And (predicate x) (x < n))
        (x IN ((Finset.range n).filter predicate))
      simp only [Finset.mem_filter, Finset.mem_range, and_comm]
    rw [hset, Set.ncard_coe_finset]
  have partial_value (n : Nat) :
      Set.partialDensity {x | predicate x} Set.univ n =
        (Nat.count predicate n : Real) / (n : Real) := by
    unfold Set.partialDensity
    simp only [Set.inter_univ, Set.univ_inter]
    rw [counts n]
    simp
  unfold HasNaturalDensity at h
  unfold Set.HasDensity
  convert h using 1
  funext n
  exact partial_value n

/-- The canonical density at k=4, obtained by the finite CRT recursion. -/
noncomputable def density (p : Nat) : Real :=
  (selectionNumerator (primesBelow p) 3 : Real) /
    ((p * (primesBelow p).prod : Nat) : Real)

theorem density_of_prime (p : Nat) (hp : p.Prime) :
    (Problem.kthPrimeFactorSet 4 p).HasDensity (density p) := by
  classical
  have period_pos : 0 < p * (primesBelow p).prod :=
    validSelectionEntries_prod_pos hp.pos (validSelectionEntries_primesBelow hp)
  have h := hasNaturalDensity_of_periodic period_pos
    (hasSelectedDivisors_periodic (primesBelow p) 3 p)
  rw [count_hasSelectedDivisors_eq_selectionNumerator p hp.pos
    (primesBelow p) (validSelectionEntries_primesBelow hp) 3] at h
  have hz := h.withoutZero
  have hpred : forall n,
      WithoutZero (HasSelectedDivisors (primesBelow p) 3 p) n IFF
        n IN Problem.kthPrimeFactorSet 4 p := by
    intro n
    by_cases hn : n = 0
    next =>
      simp [hn, WithoutZero, Problem.kthPrimeFactorSet]
    next =>
      rw [WithoutZero, HasSelectedDivisors,
        selectedDivisorCount_primesBelow p n hn]
      simp [Problem.kthPrimeFactorSet, Nat.mem_primeFactors, hp, hn,
        Nat.pos_iff_ne_zero, and_assoc]
  exact (hz.congr hpred).toSet

theorem primesBelow_pairwise_le (p : Nat) :
    (primesBelow p).Pairwise (fun a b => a <= b) := by
  exact Finset.pairwise_sort _ _

def isPrimeTrial (n : Nat) : Bool :=
  decide (2 <= n) && decide (n.minFac = n)

theorem isPrimeTrial_eq_true_iff (n : Nat) :
    Iff (isPrimeTrial n = true) n.Prime := by
  simp only [isPrimeTrial, Bool.and_eq_true, decide_eq_true_eq]
  exact Nat.prime_def_minFac.symm

def computablePrimesBelow (p : Nat) : List Nat :=
  (List.range p).filter isPrimeTrial

theorem computablePrimesBelow_perm (p : Nat) :
    (primesBelow p).Perm (computablePrimesBelow p) := by
  apply (List.perm_ext_iff_of_nodup (Finset.sort_nodup _ _)
    (List.nodup_range.filter isPrimeTrial)).2
  intro q
  simp [isPrimeTrial_eq_true_iff]

theorem primesBelow_eq_computablePrimesBelow (p : Nat) :
    primesBelow p = computablePrimesBelow p := by
  apply List.Perm.eq_of_sortedLE
    (List.Pairwise.sortedLE (primesBelow_pairwise_le p))
    (((List.pairwise_lt_range.filter isPrimeTrial).imp
      (fun h : _ < _ => Nat.le_of_lt h)).sortedLE)
  exact computablePrimesBelow_perm p

theorem prefix13 : primesBelow 13 = [2, 3, 5, 7, 11] := by
  rw [primesBelow_eq_computablePrimesBelow]
  decide +kernel
theorem prefix17 : primesBelow 17 = [2, 3, 5, 7, 11, 13] := by
  rw [primesBelow_eq_computablePrimesBelow]
  decide +kernel
theorem prefix19 : primesBelow 19 = [2, 3, 5, 7, 11, 13, 17] := by
  rw [primesBelow_eq_computablePrimesBelow]
  decide +kernel

theorem density13 : density 13 = (31 : Real) / 5005 := by
  norm_num [density, prefix13, selectionNumerator]
theorem density17 : density 17 = (206 : Real) / 36465 := by
  norm_num [density, prefix17, selectionNumerator]
theorem density19 : density 19 = (1308 : Real) / 230945 := by
  norm_num [density, prefix19, selectionNumerator]

/-- The strict valley at 13, 17, 19 contradicts every possible prime mode. -/
theorem not_unimodal : Not (Problem.IsUnimodalOnPrimes density) := by
  intro h
  let m := h.choose
  have hm := h.choose_spec
  by_cases hle : m <= 17
  next =>
    have bad := hm.2.2 17 19 (by norm_num) (by norm_num) hle (by omega)
    rw [density17, density19] at bad
    norm_num at bad
  next =>
    have bad := hm.2.1 13 17 (by norm_num) (by norm_num) (by omega)
      (by omega : 17 <= m)
    rw [density13, density17] at bad
    norm_num at bad
end E690Proof

def answer : Prop := False

/-- The exact frozen MathDB target is false; k=4 refutes its universal claim. -/
theorem solution : Problem.Target answer := by
  change False IFF _
  constructor
  next =>
    intro h
    exact False.elim h
  next =>
    intro h
    exact E690Proof.not_unimodal
      (h 4 (by decide) E690Proof.density E690Proof.density_of_prime)
end Submission
