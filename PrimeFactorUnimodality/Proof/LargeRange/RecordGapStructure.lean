import Mathlib.Data.Nat.ModEq
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Tactic.NormNum
import PrimeFactorUnimodality.Helpers.Arithmetic.FastPowMod
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordGapPrimeList
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordGapResidues

set_option autoImplicit false
set_option maxRecDepth 100000

/-!
# Structure of the certified 4,751-term composite block

The large center remains factored as a short scalar times an explicit list
product.  Most owners therefore divide it definitionally; thirteen exceptional
owners use separately replayed modular residues.
-/

namespace PrimeFactorUnimodality

inductive RecordGapResidue : Nat → Nat → Prop
  | two : RecordGapResidue 2 1
  | three : RecordGapResidue 3 2
  | five : RecordGapResidue 5 1
  | seven : RecordGapResidue 7 1
  | eleven : RecordGapResidue 11 4
  | q44983 : RecordGapResidue 44983 39717
  | q45541 : RecordGapResidue 45541 37619
  | q52103 : RecordGapResidue 52103 32377
  | q228523 : RecordGapResidue 228523 85050
  | q550631 : RecordGapResidue 550631 86302
  | q1129577 : RecordGapResidue 1129577 82320
  | q1291193 : RecordGapResidue 1291193 82500
  | q3020411447 : RecordGapResidue 3020411447 85750

theorem recordGapCenter_mod_of_residue {q r : Nat}
    (residue : RecordGapResidue q r) : recordGapCenter % q = r := by
  cases residue with
  | two => exact recordGapCenter_mod_two
  | three => exact recordGapCenter_mod_three
  | five => exact recordGapCenter_mod_five
  | seven => exact recordGapCenter_mod_seven
  | eleven => exact recordGapCenter_mod_eleven
  | q44983 => exact recordGapCenter_mod_44983
  | q45541 => exact recordGapCenter_mod_45541
  | q52103 => exact recordGapCenter_mod_52103
  | q228523 => exact recordGapCenter_mod_228523
  | q550631 => exact recordGapCenter_mod_550631
  | q1129577 => exact recordGapCenter_mod_1129577
  | q1291193 => exact recordGapCenter_mod_1291193
  | q3020411447 => exact recordGapCenter_mod_3020411447

def RecordGapOwnerSpec (d q : Nat) : Prop :=
  (q ∈ recordGapUsedTailOwners ∧ q ∣ d) ∨
    ∃ r, RecordGapResidue q r ∧ d % q = r

theorem recordGapCenter_large : 8_000_000_000 < recordGapCenter := by
  norm_num [recordGapCenter, recordGapTailProduct, recordGapPrimeList]

theorem fullRecordGap_prime_lower {q : Nat}
    (q_mem : q ∈ recordGapPrimeList) : 13 ≤ q := by
  revert q_mem
  revert q
  decide

theorem recordGapOwnerSpec_dvd_sub {d q : Nat}
    (hd : d ≤ 4_000_000_000) (owner : RecordGapOwnerSpec d q) :
    q ∣ recordGapCenter - d := by
  have d_le_center : d ≤ recordGapCenter :=
    hd.trans ((by norm_num : 4_000_000_000 ≤ 8_000_000_000).trans
      (Nat.le_of_lt recordGapCenter_large))
  rcases owner with ⟨q_mem, q_dvd_d⟩ | ⟨r, residue, d_mod⟩
  · have q_dvd_tail : q ∣ recordGapTailProduct := by
      exact List.dvd_prod (recordGapUsedTailOwners_mem q_mem)
    have q_dvd_center : q ∣ recordGapCenter := by
      exact dvd_mul_of_dvd_right q_dvd_tail 587
    apply (Nat.modEq_iff_dvd' d_le_center).mp
    exact q_dvd_d.modEq_zero_nat.trans q_dvd_center.zero_modEq_nat
  · apply (Nat.modEq_iff_dvd' d_le_center).mp
    change d % q = recordGapCenter % q
    exact ((recordGapCenter_mod_of_residue residue).trans d_mod.symm).symm

theorem recordGap_sub_not_prime {d q : Nat}
    (hd : d ≤ 4_000_000_000) (hq : 2 ≤ q) (hqBound : q ≤ 3_100_000_000)
    (owner : RecordGapOwnerSpec d q) :
    ¬(recordGapCenter - d).Prime := by
  apply Nat.not_prime_of_dvd_of_lt (recordGapOwnerSpec_dvd_sub hd owner) hq
  have hcenter : 8_000_000_000 < recordGapCenter := recordGapCenter_large
  omega

/-! The full published gap has additional archived factors beyond the compact
owner list above.  These two interfaces accept their replayed center residue
directly, so those factors need not be added to `RecordGapResidue`. -/

theorem recordGap_sub_not_prime_of_center_mod {d q r : Nat}
    (hd : d ≤ 4_000_000_000) (hq : 2 ≤ q) (hqBound : q ≤ 3_100_000_000)
    (center_mod : recordGapCenter % q = r) (d_mod : d % q = r) :
    ¬(recordGapCenter - d).Prime := by
  have d_le_center : d ≤ recordGapCenter :=
    hd.trans ((by norm_num : 4_000_000_000 ≤ 8_000_000_000).trans
      recordGapCenter_large.le)
  have q_dvd : q ∣ recordGapCenter - d := by
    apply (Nat.modEq_iff_dvd' d_le_center).mp
    exact d_mod.trans center_mod.symm
  apply Nat.not_prime_of_dvd_of_lt q_dvd hq
  have hcenter := recordGapCenter_large
  omega

theorem recordGap_add_not_prime_of_center_mod {d q r : Nat}
    (hq : 2 ≤ q) (hqBound : q ≤ 3_100_000_000)
    (center_mod : recordGapCenter % q = r)
    (d_mod : d % q = (q - r) % q) :
    ¬(recordGapCenter + d).Prime := by
  have q_dvd : q ∣ recordGapCenter + d := by
    apply (Nat.dvd_iff_mod_eq_zero).2
    rw [Nat.add_mod, center_mod, d_mod]
    have residue_lt : r < q := by
      rw [← center_mod]
      exact Nat.mod_lt _ (by omega)
    by_cases hr : r = 0
    · simp [hr]
    · have residue_pos : 0 < r := Nat.pos_of_ne_zero hr
      have hlt : q - r < q := Nat.sub_lt (by omega) residue_pos
      rw [Nat.mod_eq_of_lt hlt]
      rw [Nat.add_sub_of_le residue_lt.le, Nat.mod_self]
  apply Nat.not_prime_of_dvd_of_lt q_dvd hq
  have hcenter := recordGapCenter_large
  omega

def FullRecordGapOwnerSpec (d q : Nat) : Prop :=
  (q ∈ recordGapPrimeList ∧ q ∣ d) ∨
    ∃ r, 2 ≤ q ∧ q ≤ 3_100_000_000 ∧ recordGapCenter % q = r ∧ d % q = r

def FullRecordGapAddOwnerSpec (d q : Nat) : Prop :=
  (q ∈ recordGapPrimeList ∧ q ∣ d) ∨
    ∃ r, 2 ≤ q ∧ q ≤ 3_100_000_000 ∧ recordGapCenter % q = r ∧
      d % q = (q - r) % q

theorem fullRecordGap_sub_not_prime {d q : Nat}
    (hd : d ≤ 4_000_000_000) (owner : FullRecordGapOwnerSpec d q) :
    ¬(recordGapCenter - d).Prime := by
  rcases owner with ⟨q_mem, q_dvd_d⟩ | ⟨r, hq, q_bound, center_mod, d_mod⟩
  · have d_le_center : d ≤ recordGapCenter :=
      hd.trans ((by norm_num : 4_000_000_000 ≤ 8_000_000_000).trans
        recordGapCenter_large.le)
    have q_dvd_tail : q ∣ recordGapTailProduct := List.dvd_prod q_mem
    have q_dvd_center : q ∣ recordGapCenter := dvd_mul_of_dvd_right q_dvd_tail 587
    have q_dvd_sub : q ∣ recordGapCenter - d := by
      apply (Nat.modEq_iff_dvd' d_le_center).mp
      exact q_dvd_d.modEq_zero_nat.trans q_dvd_center.zero_modEq_nat
    apply Nat.not_prime_of_dvd_of_lt q_dvd_sub
      (by have := fullRecordGap_prime_lower q_mem; omega)
    have hcenter := recordGapCenter_large
    have hq := recordGapPrimeList_le_limit q q_mem
    omega
  · exact recordGap_sub_not_prime_of_center_mod hd (by omega) q_bound
      center_mod d_mod

theorem fullRecordGap_add_not_prime {d q : Nat}
    (owner : FullRecordGapAddOwnerSpec d q) :
    ¬(recordGapCenter + d).Prime := by
  rcases owner with ⟨q_mem, q_dvd_d⟩ | ⟨r, hq, q_bound, center_mod, d_mod⟩
  · have q_dvd_tail : q ∣ recordGapTailProduct := List.dvd_prod q_mem
    have q_dvd_center : q ∣ recordGapCenter := dvd_mul_of_dvd_right q_dvd_tail 587
    have q_dvd : q ∣ recordGapCenter + d := dvd_add q_dvd_center q_dvd_d
    apply Nat.not_prime_of_dvd_of_lt q_dvd
      (by have := fullRecordGap_prime_lower q_mem; omega)
    have hcenter := recordGapCenter_large
    have hq := recordGapPrimeList_le_limit q q_mem
    omega
  · exact recordGap_add_not_prime_of_center_mod (by omega) q_bound
      center_mod d_mod

/-- A prime occurring in the full primorial tail divides the record center.
This broader form is used by the million-term published gap, whose owner set
is much larger than the optimized 4,751-term sub-block. -/
theorem recordGap_tail_owner_dvd_center {q : Nat}
    (q_mem : q ∈ recordGapPrimeList) : q ∣ recordGapCenter := by
  have q_dvd_tail : q ∣ recordGapTailProduct := by
    exact List.dvd_prod q_mem
  exact dvd_mul_of_dvd_right q_dvd_tail 587

theorem recordGap_sub_not_prime_of_tail_owner {d q : Nat}
    (hd : d ≤ 4_000_000_000) (hq : 2 ≤ q) (hqBound : q ≤ 3_100_000_000)
    (q_mem : q ∈ recordGapPrimeList) (q_dvd_d : q ∣ d) :
    ¬(recordGapCenter - d).Prime := by
  have d_le_center : d ≤ recordGapCenter :=
    hd.trans ((by norm_num : 4_000_000_000 ≤ 8_000_000_000).trans
      recordGapCenter_large.le)
  have q_dvd_center := recordGap_tail_owner_dvd_center q_mem
  have q_dvd_sub : q ∣ recordGapCenter - d := by
    apply (Nat.modEq_iff_dvd' d_le_center).mp
    exact q_dvd_d.modEq_zero_nat.trans q_dvd_center.zero_modEq_nat
  apply Nat.not_prime_of_dvd_of_lt q_dvd_sub hq
  have hcenter := recordGapCenter_large
  have sum_lt : 4_000_000_000 + d < recordGapCenter := by
    omega
  have result_large : 4_000_000_000 < recordGapCenter - d :=
    Nat.lt_sub_of_add_lt sum_lt
  omega

theorem recordGap_add_not_prime_of_tail_owner {d q : Nat}
    (hq : 2 ≤ q) (hqBound : q ≤ 3_100_000_000)
    (q_mem : q ∈ recordGapPrimeList) (q_dvd_d : q ∣ d) :
    ¬(recordGapCenter + d).Prime := by
  have q_dvd_center := recordGap_tail_owner_dvd_center q_mem
  have q_dvd_add : q ∣ recordGapCenter + d := dvd_add q_dvd_center q_dvd_d
  apply Nat.not_prime_of_dvd_of_lt q_dvd_add hq
  have hcenter := recordGapCenter_large
  have q_lt_center : q < recordGapCenter := by
    omega
  omega

def recordGapExceptional : Nat := recordGapCenter - 84672

set_option linter.style.haveILetI false in
theorem not_prime_of_pow_ne_one {n a : Nat} (a_pos : 0 < a) (a_lt_n : a < n)
    (witness : (a : ZMod n) ^ (n - 1) ≠ 1) : ¬n.Prime := by
  intro n_prime
  letI : Fact n.Prime := ⟨n_prime⟩
  apply witness
  apply ZMod.pow_card_sub_one_eq_one
  intro a_eq_zero
  have n_dvd_a : n ∣ a := (ZMod.natCast_eq_zero_iff a n).mp a_eq_zero
  exact (not_le_of_gt a_lt_n) (Nat.le_of_dvd a_pos n_dvd_a)

theorem not_prime_of_two_pow_ne_one {n : Nat} (hn : 2 < n)
    (witness : (2 : ZMod n) ^ (n - 1) ≠ 1) : ¬n.Prime :=
  not_prime_of_pow_ne_one (by norm_num) hn witness

/-- A compact compositeness certificate: the closed modular computation is
checked by `decide`, while this theorem bridges the reusable binary algorithm
to Fermat's theorem in `ZMod`. -/
theorem not_prime_of_fastPowMod_ne_one {n a : Nat} (a_pos : 0 < a) (a_lt_n : a < n)
    (witness : fastPowMod a n (n - 1) ≠ 1) : ¬n.Prime := by
  apply not_prime_of_pow_ne_one a_pos a_lt_n
  intro pow_eq_one
  apply witness
  have cast_eq_one : ((fastPowMod a n (n - 1) : Nat) : ZMod n) = 1 := by
    rw [fastPowMod_eq_pow_mod, ZMod.natCast_mod]
    simpa only [Nat.cast_pow, Nat.cast_ofNat] using pow_eq_one
  have val_eq_one := congrArg ZMod.val cast_eq_one
  have n_pos : 0 < n := a_pos.trans a_lt_n
  have fast_lt : fastPowMod a n (n - 1) < n := by
    rw [fastPowMod_eq_pow_mod]
    exact Nat.mod_lt _ n_pos
  rw [ZMod.val_natCast_of_lt fast_lt] at val_eq_one
  rw [ZMod.val_one'' (by omega)] at val_eq_one
  exact val_eq_one

end PrimeFactorUnimodality
