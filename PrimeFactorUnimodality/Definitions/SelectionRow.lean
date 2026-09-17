import PrimeFactorUnimodality.Definitions.SelectionNumerator

set_option autoImplicit false

/-! # Bounded dynamic-programming rows for selection numerators -/

namespace PrimeFactorUnimodality

/-- Extend the tail of a bounded coefficient row while retaining the previous
coefficient needed by the admission recurrence. -/
def selectionRowTail (p previous : Nat) : List Nat → List Nat
  | [] => [previous]
  | current :: rest =>
      ((p - 1) * current + previous) :: selectionRowTail p current rest

/-- Apply one prime-admission step to a bounded coefficient row. -/
def selectionRowStep (p : Nat) : List Nat → List Nat
  | [] => []
  | first :: rest =>
      (p - 1) * first :: selectionRowTail p first rest

/-- All cleared-denominator coefficients, computed with one recursive call per
input entry. -/
def selectionRow : List Nat → List Nat
  | [] => [1]
  | p :: entries => selectionRowStep p (selectionRow entries)

private theorem selectionRowTail_length (p previous : Nat) (row : List Nat) :
    (selectionRowTail p previous row).length = row.length + 1 := by
  induction row generalizing previous with
  | nil => simp [selectionRowTail]
  | cons current rest ih => simp [selectionRowTail, ih]

private theorem selectionRowStep_length (p : Nat) (row : List Nat)
    (hrow : row ≠ []) :
    (selectionRowStep p row).length = row.length + 1 := by
  cases row with
  | nil => contradiction
  | cons first rest => simp [selectionRowStep, selectionRowTail_length]

theorem selectionRow_length (entries : List Nat) :
    (selectionRow entries).length = entries.length + 1 := by
  induction entries with
  | nil => simp [selectionRow]
  | cons p entries ih =>
      rw [selectionRow, selectionRowStep_length]
      · simp [ih]
      · intro hnil
        rw [hnil] at ih
        simp at ih

private theorem selectionRow_ne_nil (entries : List Nat) :
    selectionRow entries ≠ [] := by
  intro hnil
  have hlength := selectionRow_length entries
  simp [hnil] at hlength

private theorem selectionRowTail_getD (p previous : Nat) (row : List Nat)
    (r : Nat) (hr : r ≤ row.length) :
    (selectionRowTail p previous row).getD r 0 =
      (p - 1) * row.getD r 0 + (previous :: row).getD r 0 := by
  induction row generalizing previous r with
  | nil =>
      simp only [List.length_nil] at hr
      have : r = 0 := Nat.eq_zero_of_le_zero hr
      subst r
      simp [selectionRowTail]
  | cons current rest ih =>
      cases r with
      | zero => simp [selectionRowTail]
      | succ r =>
          simp only [selectionRowTail, List.getD_cons_succ]
          exact ih current r (by simpa using hr)

theorem selectionRowStep_getD (p : Nat) (row : List Nat)
    (hrow : row ≠ []) (r : Nat) (hr : r ≤ row.length) :
    (selectionRowStep p row).getD r 0 =
      (p - 1) * row.getD r 0 + if r = 0 then 0 else row.getD (r - 1) 0 := by
  cases row with
  | nil => contradiction
  | cons first rest =>
      cases r with
      | zero => simp [selectionRowStep]
      | succ r =>
          simp only [selectionRowStep, List.getD_cons_succ, Nat.succ_ne_zero,
            ↓reduceIte, Nat.add_sub_cancel]
          rw [selectionRowTail_getD p first rest r (by simpa using hr)]

private theorem selectionNumerator_eq_zero_of_length_lt
    (entries : List Nat) (r : Nat) (hr : entries.length < r) :
    selectionNumerator entries r = 0 := by
  induction entries generalizing r with
  | nil => cases r <;> simp_all [selectionNumerator]
  | cons p entries ih =>
      cases r with
      | zero => omega
      | succ r =>
          have hlt : entries.length < r := by simpa using hr
          rw [selectionNumerator, ih (r + 1) (hlt.trans_le (Nat.le_succ r))]
          rw [ih r hlt]
          simp

theorem selectionRow_getD (entries : List Nat) (r : Nat) :
    (selectionRow entries).getD r 0 = selectionNumerator entries r := by
  induction entries generalizing r with
  | nil => cases r <;> simp [selectionRow, selectionNumerator]
  | cons p entries ih =>
      by_cases hr : r ≤ (selectionRow entries).length
      · rw [selectionRow, selectionRowStep_getD p (selectionRow entries)
          (selectionRow_ne_nil entries) r hr]
        cases r with
        | zero =>
            rw [ih]
            simp [selectionNumerator]
        | succ r =>
            simp only [selectionNumerator, Nat.succ_ne_zero, ↓reduceIte,
              Nat.add_sub_cancel]
            rw [ih, ih]
      · have hrow : (selectionRowStep p (selectionRow entries)).length ≤ r := by
          rw [selectionRowStep_length p (selectionRow entries)
            (selectionRow_ne_nil entries)]
          omega
        rw [selectionRow]
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none hrow]
        simp only [Option.getD_none]
        have hout : (p :: entries).length < r := by
          rw [selectionRowStep_length p (selectionRow entries)
            (selectionRow_ne_nil entries), selectionRow_length] at hrow
          simp only [List.length_cons]
          omega
        exact (selectionNumerator_eq_zero_of_length_lt (p :: entries) r
          hout).symm

/-- A fixed-width dynamic-programming row containing coefficients through
degree `bound`.  Truncating after every step prevents irrelevant high-degree
coefficients from entering finite certificate computations. -/
def selectionRowBounded (bound : Nat) : List Nat → List Nat
  | [] => 1 :: List.replicate bound 0
  | p :: entries =>
      (selectionRowStep p (selectionRowBounded bound entries)).take (bound + 1)

theorem selectionRowBounded_length (bound : Nat) (entries : List Nat) :
    (selectionRowBounded bound entries).length = bound + 1 := by
  induction entries with
  | nil => simp [selectionRowBounded]
  | cons p entries ih =>
      rw [selectionRowBounded, List.length_take, selectionRowStep_length]
      · rw [ih]
        omega
      · intro hnil
        have : (selectionRowBounded bound entries).length = 0 := by simp [hnil]
        omega

theorem selectionRowBounded_getD
    (bound : Nat) (entries : List Nat) (r : Nat) (hr : r ≤ bound) :
    (selectionRowBounded bound entries).getD r 0 =
      selectionNumerator entries r := by
  induction entries generalizing r with
  | nil =>
      cases r with
      | zero => simp [selectionRowBounded, selectionNumerator]
      | succ r =>
          have hlt : r < bound := by omega
          simp [selectionRowBounded, selectionNumerator,
            List.getD_eq_getElem?_getD, hlt]
  | cons p entries ih =>
      rw [selectionRowBounded, List.getD_eq_getElem?_getD,
        List.getElem?_take_of_lt (by omega)]
      rw [← List.getD_eq_getElem?_getD]
      rw [selectionRowStep_getD p (selectionRowBounded bound entries)
        (by
          intro hnil
          have hlength := selectionRowBounded_length bound entries
          simp [hnil] at hlength)
        r (by rw [selectionRowBounded_length]; omega)]
      cases r with
      | zero =>
          rw [ih 0 (by omega)]
          simp [selectionNumerator]
      | succ r =>
          simp only [Nat.succ_ne_zero, ↓reduceIte, Nat.add_sub_cancel]
          rw [ih (r + 1) (by omega), ih r (by omega)]
          simp [selectionNumerator]

end PrimeFactorUnimodality
