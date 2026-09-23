import Mathlib.Data.List.Chain
import PrimeFactorUnimodality.Helpers.Analytic.DirichletMomentBlocks

/-! # Ordered coverage of all grouped moment indices

Coverage is checked from consecutive natural endpoints, not by replaying
every integer in the full prefix. Distinct group labels identify the exact
fiber of the semantic bin function. Adjacent same-label chunks are merged
with the preceding block assembler before forming this partition.
-/

namespace PrimeFactorUnimodality.DirichletMomentBlock

open Finset

variable {degree : ℕ}

/-- Consecutive ordered blocks cover one half-open natural interval without gaps. -/
def Chain (lo hi : ℕ) : List (DirichletMomentBlock degree) → Prop
  | [] => lo = hi
  | r :: rows => r.first = lo ∧ r.first ≤ r.stop ∧ Chain r.stop hi rows

/-- Coverage is a bounded list of endpoint comparisons. -/
def checkChain (lo hi : ℕ) : List (DirichletMomentBlock degree) → Bool
  | [] => decide (lo = hi)
  | r :: rows => decide (r.first = lo ∧ r.first ≤ r.stop) && checkChain r.stop hi rows

/-- The executable endpoint check proves the exact coverage relation. -/
theorem checkChain_eq_true (lo hi : ℕ) (rows : List (DirichletMomentBlock degree)) :
    checkChain lo hi rows = true ↔ Chain lo hi rows := by
  induction rows generalizing lo with
  | nil => simp [checkChain, Chain]
  | cons r rows ih => simp [checkChain, Chain, ih, and_assoc]

/-- Adjacent decreasing labels certify uniqueness without pairwise duplicate scanning. -/
def checkGroups (rows : List (DirichletMomentBlock degree)) : Bool :=
  decide ((rows.map group).IsChain (fun a b => b < a))

/-- Transitivity turns the adjacent label checks into global uniqueness. -/
theorem nodup_of_checkGroups {rows : List (DirichletMomentBlock degree)}
    (h : checkGroups rows = true) : (rows.map group).Nodup := by
  have hc : (rows.map group).IsChain (fun a b => b < a) := of_decide_eq_true h
  have hp := List.isChain_iff_pairwise.mp hc
  exact hp.imp (fun hab => ne_of_gt hab)

/-- One linear pass over endpoints and one over adjacent labels validate the partition. -/
def checkPartition (lo hi : ℕ) (rows : List (DirichletMomentBlock degree)) : Bool :=
  checkChain lo hi rows && checkGroups rows

/-- Both exact coverage and global label uniqueness follow from the compact check. -/
theorem checkPartition_sound (lo hi : ℕ) (rows : List (DirichletMomentBlock degree))
    (h : checkPartition lo hi rows = true) :
    Chain lo hi rows ∧ (rows.map group).Nodup := by
  simp only [checkPartition, Bool.and_eq_true] at h
  exact ⟨(checkChain_eq_true lo hi rows).mp h.1, nodup_of_checkGroups h.2⟩

/-- Coverage chunks compose solely at their common endpoint. -/
theorem Chain.append {lo mid hi : ℕ} {left right : List (DirichletMomentBlock degree)}
    (hl : Chain lo mid left) (hr : Chain mid hi right) : Chain lo hi (left ++ right) := by
  induction left generalizing lo with
  | nil =>
    change lo = mid at hl
    subst lo
    exact hr
  | cons r rows ih => exact ⟨hl.1, hl.2.1, ih hl.2.2⟩

/-- A chain has ordered outer endpoints, even when some blocks are empty. -/
theorem Chain.ordered {lo hi : ℕ} {rows : List (DirichletMomentBlock degree)}
    (h : Chain lo hi rows) : lo ≤ hi := by
  induction rows generalizing lo with
  | nil => exact (show lo = hi from h).le
  | cons r rows ih => exact h.1 ▸ h.2.1.trans (ih h.2.2)

/-- Every member block lies inside the chain's endpoints. -/
theorem Chain.bounds {lo hi : ℕ} {rows : List (DirichletMomentBlock degree)}
    (h : Chain lo hi rows) {r : DirichletMomentBlock degree} (hr : r ∈ rows) :
    lo ≤ r.first ∧ r.stop ≤ hi := by
  induction rows generalizing lo with
  | nil => simp at hr
  | cons a rows ih =>
    rcases List.mem_cons.mp hr with rfl | hr
    · exact ⟨h.1.ge, h.2.2.ordered⟩
    · have ht := ih h.2.2 hr
      exact ⟨(h.1 ▸ h.2.1).trans ht.1, ht.2⟩

/-- Semantic bin lookup; numerical atom computations already know their common group. -/
def binAt : List (DirichletMomentBlock degree) → ℕ → ℤ
  | [], _ => 0
  | r :: rows, n => if n < r.stop then r.group else binAt rows n

/-- Every covered integer is assigned to a block actually containing it. -/
theorem Chain.select {lo hi : ℕ} {rows : List (DirichletMomentBlock degree)}
    (h : Chain lo hi rows) {n : ℕ} (hn : lo ≤ n ∧ n < hi) :
    ∃ r ∈ rows, n ∈ Ico r.first r.stop ∧ binAt rows n = r.group := by
  induction rows generalizing lo with
  | nil => have he : lo = hi := h; omega
  | cons r rows ih =>
    by_cases hm : n < r.stop
    · exact ⟨r, by simp, mem_Ico.mpr ⟨h.1.symm ▸ hn.1, hm⟩, by simp [binAt, hm]⟩
    · obtain ⟨a, ha, hna, hbin⟩ := ih h.2.2 ⟨by omega, hn.2⟩
      exact ⟨a, by simp [ha], hna, by simpa [binAt, hm] using hbin⟩

/-- No preceding block can steal an integer from a later block's interval. -/
theorem Chain.binAt_eq {lo hi : ℕ} {rows : List (DirichletMomentBlock degree)}
    (h : Chain lo hi rows) {r : DirichletMomentBlock degree} (hr : r ∈ rows)
    {n : ℕ} (hn : n ∈ Ico r.first r.stop) : binAt rows n = r.group := by
  induction rows generalizing lo with
  | nil => simp at hr
  | cons a rows ih =>
    rcases List.mem_cons.mp hr with rfl | hr
    · simp [binAt, (mem_Ico.mp hn).2]
    · have hnlo := (h.2.2.bounds hr).1.trans (mem_Ico.mp hn).1
      simpa [binAt, not_lt.mpr hnlo] using ih h.2.2 hr

/-- Distinct labels make each full-prefix frequency fiber exactly its corresponding block. -/
theorem Chain.filter_eq {lo hi : ℕ} {rows : List (DirichletMomentBlock degree)}
    (h : Chain lo hi rows) (hlabels : (rows.map group).Nodup)
    {r : DirichletMomentBlock degree} (hr : r ∈ rows) :
    ((Ico lo hi).filter (fun n => binAt rows n = r.group)) = Ico r.first r.stop := by
  ext n
  constructor
  · intro hn
    obtain ⟨hn, hb⟩ := mem_filter.mp hn
    obtain ⟨a, ha, hna, hbin⟩ := h.select (mem_Ico.mp hn)
    have he : a = r := List.inj_on_of_nodup_map hlabels ha hr (hbin.symm.trans hb)
    simpa [he] using hna
  · intro hn
    have hb := h.bounds hr
    exact mem_filter.mpr ⟨mem_Ico.mpr
      ⟨hb.1.trans (mem_Ico.mp hn).1, (mem_Ico.mp hn).2.trans_le hb.2⟩,
      h.binAt_eq hr hn⟩

end PrimeFactorUnimodality.DirichletMomentBlock
