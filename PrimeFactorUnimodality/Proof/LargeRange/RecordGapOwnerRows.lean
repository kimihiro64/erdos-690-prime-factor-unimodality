/-
Copyright (c) 2026 Jonas Whidden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonas Whidden
-/
import PrimeFactorUnimodality.Proof.LargeRange.RecordGapStructure

set_option autoImplicit false

/-! # Compact row interface for the full record-gap certificate

This module is the non-generated boundary for replacing the generated forest
of per-offset binary case trees.  A generated row should define a computable
owner function and prove its bounded validity once.  The generic conversion
and cover theorems below then provide the block statements consumed by
`FullRecordRange`.

Fermat exceptions can be packaged directly as `FullRecordGapSubRow` or
`FullRecordGapAddRow`; divisor and residue entries should use the more compact
owner-row structures.  No certificate data belongs in this module.
-/

namespace PrimeFactorUnimodality

/-- The two forms of elementary evidence used for non-Fermat gap entries. -/
inductive FullRecordGapOwner where
  | tail (q : Nat)
  | residue (q r : Nat)

namespace FullRecordGapOwner

def ValidSub (owner : FullRecordGapOwner) (d : Nat) : Prop :=
  match owner with
  | .tail q => q ∈ recordGapPrimeList ∧ q ∣ d
  | .residue q r =>
      2 ≤ q ∧ q ≤ 100_000_000_000 ∧ recordGapCenter % q = r ∧ d % q = r

def ValidAdd (owner : FullRecordGapOwner) (d : Nat) : Prop :=
  match owner with
  | .tail q => q ∈ recordGapPrimeList ∧ q ∣ d
  | .residue q r =>
      2 ≤ q ∧ q ≤ 100_000_000_000 ∧ recordGapCenter % q = r ∧
        d % q = (q - r) % q

theorem sub_not_prime {owner : FullRecordGapOwner} {d : Nat}
    (hd : d ≤ 4_000_000_000) (valid : owner.ValidSub d) :
    ¬(recordGapCenter - d).Prime := by
  cases owner with
  | tail q =>
      apply fullRecordGap_sub_not_prime (q := q) hd
      exact Or.inl (by simpa [ValidSub] using valid)
  | residue q r =>
      apply fullRecordGap_sub_not_prime (q := q) hd
      exact Or.inr ⟨r, by simpa [ValidSub] using valid⟩

theorem add_not_prime {owner : FullRecordGapOwner} {d : Nat}
    (valid : owner.ValidAdd d) : ¬(recordGapCenter + d).Prime := by
  cases owner with
  | tail q =>
      apply fullRecordGap_add_not_prime (q := q)
      exact Or.inl (by simpa [ValidAdd] using valid)
  | residue q r =>
      apply fullRecordGap_add_not_prime (q := q)
      exact Or.inr ⟨r, by simpa [ValidAdd] using valid⟩

end FullRecordGapOwner

/-- One bounded subtraction row with a compact owner function. -/
structure FullRecordGapSubOwnerRow where
  lower : Nat
  upper : Nat
  upper_le_gap : upper ≤ 455703
  owner : Nat → FullRecordGapOwner
  valid : ∀ d, lower ≤ d → d ≤ upper → (owner d).ValidSub d

/-- One bounded addition row with a compact owner function. -/
structure FullRecordGapAddOwnerRow where
  lower : Nat
  upper : Nat
  owner : Nat → FullRecordGapOwner
  valid : ∀ d, lower ≤ d → d ≤ upper → (owner d).ValidAdd d

/-- A subtraction row after all elementary or Fermat evidence is assembled. -/
structure FullRecordGapSubRow where
  lower : Nat
  upper : Nat
  not_prime : ∀ d, lower ≤ d → d ≤ upper → ¬(recordGapCenter - d).Prime

/-- An addition row after all elementary or Fermat evidence is assembled. -/
structure FullRecordGapAddRow where
  lower : Nat
  upper : Nat
  not_prime : ∀ d, lower ≤ d → d ≤ upper → ¬(recordGapCenter + d).Prime

def FullRecordGapSubOwnerRow.toRow
    (row : FullRecordGapSubOwnerRow) : FullRecordGapSubRow where
  lower := row.lower
  upper := row.upper
  not_prime := fun d hdLower hdUpper => by
    apply FullRecordGapOwner.sub_not_prime
      (hdUpper.trans (row.upper_le_gap.trans (by norm_num)))
    exact row.valid d hdLower hdUpper

def FullRecordGapAddOwnerRow.toRow
    (row : FullRecordGapAddOwnerRow) : FullRecordGapAddRow where
  lower := row.lower
  upper := row.upper
  not_prime := fun d hdLower hdUpper =>
    FullRecordGapOwner.add_not_prime (row.valid d hdLower hdUpper)

def FullRecordGapSubRowsCover
    (rows : List FullRecordGapSubRow) (lower upper : Nat) : Prop :=
  ∀ d, lower ≤ d → d ≤ upper →
    ∃ row ∈ rows, row.lower ≤ d ∧ d ≤ row.upper

def FullRecordGapAddRowsCover
    (rows : List FullRecordGapAddRow) (lower upper : Nat) : Prop :=
  ∀ d, lower ≤ d → d ≤ upper →
    ∃ row ∈ rows, row.lower ≤ d ∧ d ≤ row.upper

theorem fullRecordGapSubBlock_of_rows
    {rows : List FullRecordGapSubRow}
    (cover : FullRecordGapSubRowsCover rows 1 455703) :
    ∀ d, 1 ≤ d → d ≤ 455703 → ¬(recordGapCenter - d).Prime := by
  intro d hdLower hdUpper
  obtain ⟨row, _, rowLower, rowUpper⟩ := cover d hdLower hdUpper
  exact row.not_prime d rowLower rowUpper

theorem fullRecordGapAddBlock_of_rows
    {rows : List FullRecordGapAddRow}
    (cover : FullRecordGapAddRowsCover rows 1 657401) :
    ∀ d, 1 ≤ d → d ≤ 657401 → ¬(recordGapCenter + d).Prime := by
  intro d hdLower hdUpper
  obtain ⟨row, _, rowLower, rowUpper⟩ := cover d hdLower hdUpper
  exact row.not_prime d rowLower rowUpper

end PrimeFactorUnimodality
