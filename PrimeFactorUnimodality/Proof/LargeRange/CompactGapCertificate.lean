module
public import Mathlib.FieldTheory.Finite.Basic
public import PrimeFactorUnimodality.Helpers.Arithmetic.EagerDecide
public import PrimeFactorUnimodality.Helpers.Arithmetic.PowModCheckpoint
public import PrimeFactorUnimodality.Proof.LargeRange.Generated.FullRecordGapCenterValue

set_option autoImplicit false

/-! # Checked positional rows for the full record gap

Each entry gives a proper divisor, or zero for a Fermat test. Positions supply
the offsets, so completeness follows from row lengths and adjacent intervals.
-/

public section
namespace PrimeFactorUnimodality

@[expose] def compactGapNumber (add : Bool) (d : Nat) : Nat :=
  if add then fullRecordGapCenterValue + d else fullRecordGapCenterValue - d

@[expose] def compactGapEntry (n q : Nat) : Bool :=
  decide (2 ≤ q ∧ q < n ∧ n % q = 0)

theorem compactGapEntry_sound {n q : Nat} (h : compactGapEntry n q = true) :
    ¬n.Prime := by
  obtain ⟨hq, hlt, hmod⟩ := of_decide_eq_true h
  exact Nat.not_prime_of_dvd_of_lt (Nat.dvd_of_mod_eq_zero hmod) hq hlt

inductive CompactGapComposites : List Nat → Prop
  | nil : CompactGapComposites []
  | cons {n ns} : ¬n.Prime → CompactGapComposites ns → CompactGapComposites (n :: ns)

theorem compactGapFermat_sound (n r : Nat) (power : PowModState 3 n (n - 1) r)
    (check : decide (3 < n ∧ r ≠ 1) = true) : ¬n.Prime := by
  obtain ⟨hn, hr⟩ := of_decide_eq_true check
  intro prime
  have coprime : Nat.Coprime 3 n := (prime.coprime_iff_not_dvd.mpr
    (Nat.not_dvd_of_pos_of_lt (by decide) hn)).symm
  have h := Nat.ModEq.pow_card_sub_one_eq_one prime coprime
  have h' : 3 ^ (n - 1) % n = 1 := by
    simpa only [Nat.ModEq, Nat.mod_eq_of_lt (show 1 < n by omega)] using h
  exact hr (power.eq.symm.trans h')

@[expose] def compactGapExceptions (add : Bool) : Nat → List Nat → List Nat
  | _, [] => []
  | start, q :: qs =>
    if q = 0 then compactGapNumber add start :: compactGapExceptions add (start + 1) qs
    else compactGapExceptions add (start + 1) qs

@[expose] def compactGapCheck (add : Bool) : Nat → List Nat → Bool
  | _, [] => true
  | start, q :: qs => (q == 0 || compactGapEntry (compactGapNumber add start) q) &&
      compactGapCheck add (start + 1) qs

@[expose] def CompactGapBlock (add : Bool) (start stop : Nat) : Prop :=
  ∀ d, start ≤ d → d < stop → ¬(compactGapNumber add d).Prime

theorem compactGapCheck_sound (add : Bool) (start : Nat) (qs : List Nat)
    (h : compactGapCheck add start qs = true)
    (exceptions : CompactGapComposites (compactGapExceptions add start qs)) :
    CompactGapBlock add start (start + qs.length) := by
  induction qs generalizing start with
  | nil => intro d hd hu; simp at hu; omega
  | cons q qs ih =>
    have both : (q == 0 || compactGapEntry (compactGapNumber add start) q) = true ∧
        compactGapCheck add (start + 1) qs = true := by
      simpa only [compactGapCheck, Bool.and_eq_true] using h
    obtain ⟨head, tail⟩ := both
    have hn : ¬(compactGapNumber add start).Prime := by
      by_cases hq : q = 0
      · simp only [compactGapExceptions, hq, ↓reduceIte] at exceptions
        cases exceptions with | cons hn _ => exact hn
      · apply compactGapEntry_sound
        simpa [hq] using head
    have rest : CompactGapComposites (compactGapExceptions add (start + 1) qs) := by
      by_cases hq : q = 0
      · simp only [compactGapExceptions, hq, ↓reduceIte] at exceptions
        cases exceptions with | cons _ ht => exact ht
      · simpa only [compactGapExceptions, hq, ↓reduceIte] using exceptions
    intro d hd hu
    by_cases he : d = start
    · subst d
      exact hn
    · apply ih (start + 1) tail rest d (by omega)
      simpa only [List.length_cons] using (show d < start + 1 + qs.length by
        simp only [List.length_cons] at hu
        omega)

theorem compactGapBlock_append {add : Bool} {lo mid hi : Nat}
    (left : CompactGapBlock add lo mid) (right : CompactGapBlock add mid hi) :
    CompactGapBlock add lo hi := by
  intro d hd hu
  by_cases hm : d < mid
  · exact left d hd hm
  · exact right d (by omega) hu

end PrimeFactorUnimodality
