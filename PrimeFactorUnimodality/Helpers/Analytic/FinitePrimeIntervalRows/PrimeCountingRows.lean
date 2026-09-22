import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.EndpointBounds
import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.PrimeCountingNumerics
import PrimeFactorUnimodality.Helpers.FiniteCertificates.ComputablePrimePrefix

set_option autoImplicit false
set_option maxRecDepth 10000

/-! # PrimeCountingRows

Prime-counting endpoint enclosures and their finite-range assemblers.
-/

namespace PrimeFactorUnimodality

noncomputable section

structure DusartPrimeCountingRow where
  left : Nat
  right : Nat
  left_large : 2 ≤ left
  left_le_right : left ≤ right
  lower : ∀ x : Real, (599 : Real) ≤ x → (left : Real) ≤ x →
    x ≤ right →
    dusartPiLower x ≤ (Nat.primeCounting ⌊x⌋₊ : Real)
  upper : ∀ x : Real, (left : Real) ≤ x → x ≤ right →
    (Nat.primeCounting ⌊x⌋₊ : Real) ≤ dusartPiUpper x

structure DusartPrimeCountingEndpointRow where
  left : Nat
  right : Nat
  left_large : 599 ≤ left
  left_le_right : left ≤ right
  lower_endpoint : dusartPiLower right ≤ (Nat.primeCounting left : Real)
  upper_endpoint : (Nat.primeCounting right : Real) ≤ dusartPiUpper left

/-! A first nontrivial endpoint row, proved from the exact finite prime count
and elementary logarithm envelopes.  The row is deliberately a singleton:
it is a kernel-checked seed for the eventual interval-table generator. -/
def dusartPrimeCountingEndpointRow_1000 :
    DusartPrimeCountingEndpointRow := by
  have hcount : Nat.primeCounting 1000 = 168 := by
    rw [← computablePrimesBelow_succ_length]
    decide +kernel
  have hlog_eq : Real.log (1000 : Real) = 3 * (Real.log 2 + Real.log 5) := by
    rw [show (1000 : Real) = (2 * 5) ^ (3 : Nat) by norm_num,
      Real.log_pow, Real.log_mul (by norm_num) (by norm_num)]
    norm_num
  have hlog_lower :
      (3 : Real) * (693147 / 1000000) +
        (3 : Real) * (1609437 / 1000000) ≤ Real.log 1000 := by
    nlinarith [Real.log_two_gt_d9, Real.log_five_gt_d9]
  have hlog_upper : Real.log 1000 ≤
      (3 : Real) * (693148 / 1000000) +
        (3 : Real) * (1609438 / 1000000) := by
    nlinarith [Real.log_two_lt_d9, Real.log_five_lt_d9]
  have hlog_pos : 0 < Real.log (1000 : Real) :=
    Real.log_pos (by norm_num)
  refine {
    left := 1000
    right := 1000
    left_large := by norm_num
    left_le_right := le_rfl
    lower_endpoint := ?_
    upper_endpoint := ?_ }
  · rw [hcount]
    apply dusartPiLower_le_of_log_lower (by norm_num) (by norm_num) hlog_lower
    norm_num
  · rw [hcount]
    apply le_dusartPiUpper_of_log_upper (by norm_num) hlog_pos hlog_upper
    norm_num

def DusartPrimeCountingEndpointRowsCoverFrom599
    (rows : List DusartPrimeCountingEndpointRow) (X : Real) : Prop :=
  ∀ x : Real, (599 : Real) ≤ x → x ≤ X →
    ∃ row ∈ rows, (row.left : Real) ≤ x ∧ x ≤ row.right

theorem dusartPrimeCountingEndpointRow_1000_cover :
    ∀ x : Real, (1000 : Real) ≤ x → x ≤ 1000 →
      ∃ row ∈ [dusartPrimeCountingEndpointRow_1000],
        (row.left : Real) ≤ x ∧ x ≤ row.right := by
  intro x hx hX
  have hx1000 : x = 1000 := by linarith
  subst x
  exact ⟨dusartPrimeCountingEndpointRow_1000, by simp, le_rfl, le_rfl⟩

def DusartPrimeCountingEndpointIndexedCoverFrom599 {n : Nat}
    (rows : Fin n → DusartPrimeCountingEndpointRow) (X : Real) : Prop :=
  ∀ x : Real, (599 : Real) ≤ x → x ≤ X →
    ∃ i : Fin n, (rows i).left ≤ x ∧ x ≤ (rows i).right

theorem dusartPrimeCountingEndpointIndexedCover_of_list
    {X : Real} {rows : List DusartPrimeCountingEndpointRow}
    (cover : DusartPrimeCountingEndpointRowsCoverFrom599 rows X) :
    DusartPrimeCountingEndpointIndexedCoverFrom599
      (fun i : Fin rows.length => rows.get i) X := by
  exact indexed_interval_cover_of_list_cover rows
    (fun row => row.left) (fun row => row.right) cover

theorem dusartPrimeCountingEndpointIndexedCoverFrom599_append
    {m X : Real} {n₁ n₂ : Nat}
    {left : Fin n₁ → DusartPrimeCountingEndpointRow}
    {right : Fin n₂ → DusartPrimeCountingEndpointRow}
    (hleft : DusartPrimeCountingEndpointIndexedCoverFrom599 left m)
    (hright : DusartPrimeCountingEndpointIndexedCoverFrom599 right X) :
    DusartPrimeCountingEndpointIndexedCoverFrom599
      (Fin.append left right) X := by
  intro x hx hX
  exact indexed_interval_cover_append (Q := fun _ => True) left right
    (fun row => row.left) (fun row => row.right)
    (fun y hy _ hym => hleft y hy hym)
    (fun y hy _ hym hyX => hright y hy hyX)
    x hx trivial hX

/-! Compact indexed chunks for the bounded prime-counting endpoint table. -/
structure DusartPrimeCountingEndpointChunk where
  n : Nat
  cutoff : Real
  rows : Fin n → DusartPrimeCountingEndpointRow
  cover : DusartPrimeCountingEndpointIndexedCoverFrom599 rows cutoff

def DusartPrimeCountingEndpointChunk.of_list
    {rows : List DusartPrimeCountingEndpointRow} {cutoff : Real}
    (cover : DusartPrimeCountingEndpointRowsCoverFrom599 rows cutoff) :
    DusartPrimeCountingEndpointChunk :=
  { n := rows.length
    cutoff := cutoff
    rows := fun i => rows.get i
    cover := dusartPrimeCountingEndpointIndexedCover_of_list cover }

def DusartPrimeCountingEndpointChunk.append
    (left right : DusartPrimeCountingEndpointChunk) :
    DusartPrimeCountingEndpointChunk :=
  { n := left.n + right.n
    cutoff := right.cutoff
    rows := Fin.append left.rows right.rows
    cover := dusartPrimeCountingEndpointIndexedCoverFrom599_append
      left.cover right.cover }

def DusartPrimeCountingEndpointChunk.appendMany
    (first : DusartPrimeCountingEndpointChunk)
    (rest : List DusartPrimeCountingEndpointChunk) :
    DusartPrimeCountingEndpointChunk :=
  match rest with
  | [] => first
  | next :: tail =>
      DusartPrimeCountingEndpointChunk.appendMany
        (DusartPrimeCountingEndpointChunk.append first next) tail

theorem dusartPrimeCountingEndpointRow_provides
    (row : DusartPrimeCountingEndpointRow) {x : Real}
    (hleft : (row.left : Real) ≤ x) (hright : x ≤ row.right) :
    dusartPiLower x ≤ (Nat.primeCounting ⌊x⌋₊ : Real) ∧
      (Nat.primeCounting ⌊x⌋₊ : Real) ≤ dusartPiUpper x := by
  have hleft599 : (599 : Real) ≤ row.left := by exact_mod_cast row.left_large
  have hright599 : (599 : Real) ≤ (row.right : Real) :=
    hleft599.trans (by exact_mod_cast row.left_le_right)
  have hfloor_left : row.left ≤ ⌊x⌋₊ := Nat.le_floor hleft
  have hfloor_right : ⌊x⌋₊ ≤ row.right := Nat.floor_le_of_le hright
  have hpi_left : (Nat.primeCounting row.left : Real) ≤
      (Nat.primeCounting ⌊x⌋₊ : Real) := by
    exact_mod_cast Nat.monotone_primeCounting hfloor_left
  have hpi_right : (Nat.primeCounting ⌊x⌋₊ : Real) ≤
      (Nat.primeCounting row.right : Real) := by
    exact_mod_cast Nat.monotone_primeCounting hfloor_right
  have hlower : dusartPiLower x ≤ dusartPiLower (row.right : Real) :=
    dusartPiLower_monotoneOn (hleft599.trans hleft)
      (by exact hright599) hright
  have hupper : dusartPiUpper (row.left : Real) ≤ dusartPiUpper x :=
    dusartPiUpper_monotoneOn (by norm_num at hleft599 ⊢; linarith)
      (by change (10 : Real) ≤ x; linarith) hleft
  constructor
  · exact hlower.trans (row.lower_endpoint.trans hpi_left)
  · exact hpi_right.trans (row.upper_endpoint.trans hupper)

theorem hasDusartRealPrimeCountingBoundsBelow_of_indexed_endpoint_rows
    {n : Nat} {X : Real}
    {rows : Fin n → DusartPrimeCountingEndpointRow}
    (cover : DusartPrimeCountingEndpointIndexedCoverFrom599 rows X)
    (smallUpper : ∀ x : Real, 2 ≤ x → x < 599 →
      (Nat.primeCounting ⌊x⌋₊ : Real) ≤ dusartPiUpper x) :
    HasDusartRealPrimeCountingBoundsBelow X := by
  constructor
  · intro x hx hX
    obtain ⟨i, hleft, hright⟩ := cover x hx hX
    exact (dusartPrimeCountingEndpointRow_provides (rows i) hleft hright).1
  · intro x hx hX
    by_cases hsmall : x < 599
    · exact smallUpper x hx hsmall
    · obtain ⟨i, hleft, hright⟩ := cover x
        (le_of_not_gt hsmall) hX
      exact (dusartPrimeCountingEndpointRow_provides (rows i) hleft hright).2

theorem hasDusartRealPrimeCountingBoundsBelow_of_endpoint_chunk
    (chunk : DusartPrimeCountingEndpointChunk)
    (smallUpper : ∀ x : Real, 2 ≤ x → x < 599 →
      (Nat.primeCounting ⌊x⌋₊ : Real) ≤ dusartPiUpper x) :
    HasDusartRealPrimeCountingBoundsBelow chunk.cutoff := by
  exact hasDusartRealPrimeCountingBoundsBelow_of_indexed_endpoint_rows
    chunk.cover smallUpper

theorem hasDusartRealPrimeCountingBoundsBelow_of_endpoint_chunks
    (first : DusartPrimeCountingEndpointChunk)
    (rest : List DusartPrimeCountingEndpointChunk)
    (smallUpper : ∀ x : Real, 2 ≤ x → x < 599 →
      (Nat.primeCounting ⌊x⌋₊ : Real) ≤ dusartPiUpper x) :
    HasDusartRealPrimeCountingBoundsBelow
      (DusartPrimeCountingEndpointChunk.appendMany first rest).cutoff := by
  induction rest generalizing first with
  | nil =>
      exact hasDusartRealPrimeCountingBoundsBelow_of_endpoint_chunk
        first smallUpper
  | cons next tail ih =>
      exact ih (DusartPrimeCountingEndpointChunk.append first next)

theorem dusartPrimeCountingEndpointRowsCoverFrom599_append
    {m X : Real} {left right : List DusartPrimeCountingEndpointRow}
    (hleft : DusartPrimeCountingEndpointRowsCoverFrom599 left m)
    (hright : DusartPrimeCountingEndpointRowsCoverFrom599 right X) :
    DusartPrimeCountingEndpointRowsCoverFrom599 (left ++ right) X := by
  intro x hx hX
  by_cases hxm : x ≤ m
  · obtain ⟨row, hrow, hleft_row, hright_row⟩ := hleft x hx hxm
    exact ⟨row, by simp [hrow], hleft_row, hright_row⟩
  · obtain ⟨row, hrow, hleft_row, hright_row⟩ := hright x hx hX
    exact ⟨row, by simp [hrow], hleft_row, hright_row⟩

theorem hasDusartRealPrimeCountingBoundsBelow_of_endpoint_rows
    {X : Real} {rows : List DusartPrimeCountingEndpointRow}
    (cover : DusartPrimeCountingEndpointRowsCoverFrom599 rows X)
    (smallUpper : ∀ x : Real, 2 ≤ x → x < 599 →
      (Nat.primeCounting ⌊x⌋₊ : Real) ≤ dusartPiUpper x) :
    HasDusartRealPrimeCountingBoundsBelow X := by
  constructor
  · intro x hx hX
    obtain ⟨row, hrow, hleft, hright⟩ := cover x hx hX
    exact (dusartPrimeCountingEndpointRow_provides row hleft hright).1
  · intro x hx hX
    by_cases hsmall : x < 599
    · exact smallUpper x hx hsmall
    · obtain ⟨row, hrow, hleft, hright⟩ := cover x
        (le_of_not_gt hsmall) hX
      exact (dusartPrimeCountingEndpointRow_provides row hleft hright).2

def DusartPrimeCountingRowsCoverUpTo
    (rows : List DusartPrimeCountingRow) (X : Real) : Prop :=
  ∀ x : Real, 2 ≤ x → x ≤ X →
    ∃ row ∈ rows, (row.left : Real) ≤ x ∧ x ≤ row.right

/-! The lower Dusart estimate starts only at `599`.  This variant keeps that
fact visible, so the finite table need not carry rows whose only purpose is
to establish the lower bound below `599`; the short upper range is supplied
by a separate elementary or computational lemma. -/
def DusartPrimeCountingRowsCoverFrom599
    (rows : List DusartPrimeCountingRow) (X : Real) : Prop :=
  ∀ x : Real, (599 : Real) ≤ x → x ≤ X →
    ∃ row ∈ rows, (row.left : Real) ≤ x ∧ x ≤ row.right

theorem hasDusartRealPrimeCountingBoundsBelow_of_rows_from599
    {X : Real} {rows : List DusartPrimeCountingRow}
    (cover : DusartPrimeCountingRowsCoverFrom599 rows X)
    (smallUpper : ∀ x : Real, 2 ≤ x → x < 599 →
      (Nat.primeCounting ⌊x⌋₊ : Real) ≤ dusartPiUpper x) :
    HasDusartRealPrimeCountingBoundsBelow X := by
  constructor
  · intro x hx hX
    obtain ⟨row, hrow, hleft, hright⟩ := cover x hx hX
    exact row.lower x hx hleft hright
  · intro x hx hX
    by_cases hsmall : x < 599
    · exact smallUpper x hx hsmall
    · obtain ⟨row, hrow, hleft, hright⟩ := cover x
        (le_of_not_gt hsmall) hX
      exact row.upper x hleft hright

theorem hasDusartRealPrimeCountingBoundsBelow_of_rows
    {X : Real} {rows : List DusartPrimeCountingRow}
    (cover : DusartPrimeCountingRowsCoverUpTo rows X) :
    HasDusartRealPrimeCountingBoundsBelow X := by
  constructor
  · intro x hx hX
    obtain ⟨row, hrow, hleft, hright⟩ := cover x (by linarith) hX
    exact row.lower x hx hleft hright
  · intro x hx hX
    obtain ⟨row, hrow, hleft, hright⟩ := cover x hx hX
    exact row.upper x hleft hright

end

end PrimeFactorUnimodality
