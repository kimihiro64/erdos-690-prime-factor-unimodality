import PrimeFactorUnimodality.Helpers.Analytic.CheckedXiGridSigns
import PrimeFactorUnimodality.Helpers.Analytic.TuringMarginIntervals

/-! # Shared checked endpoint blocks feed actual Turing completeness

Sample endpoints are stored once and reused by adjacent rows. A linear
adjacent-order check gives global strict ordering through Mathlib's finite
order theorem. Sign checks feed the existing ordered-row predicate, whose
append and completed-area lemmas remain unchanged. Placement and a checked
Turing margin supply the actual low-height completeness conclusion.
-/

namespace PrimeFactorUnimodality

open Fourier

/-- One retained endpoint vector for a block of consecutive sign rows. -/
structure XiGridSignBlock (n : ℕ) where
  sample : Vector XiGridSignData (n + 1)

/-- The exact rational ordinate represented by a retained signed index. -/
def XiGridSignBlock.ordinate {n : ℕ} (s : XiGridSignBlock n) (base span : ℚ) (levels : ℕ)
    (i : Fin (n + 1)) : ℚ :=
  rationalGridHeight base span levels (s.sample[i.val].point.index)

/-- Adjacent rows share their rational endpoints rather than duplicating them. -/
def XiGridSignBlock.rows {n : ℕ} (s : XiGridSignBlock n) (base span : ℚ) (levels : ℕ) :
    Fin n → XiSignRow := XiSignRows.ofEndpoints (s.ordinate base span levels)

/-- Check each sample once and only adjacent index/sign pairs for block ordering. -/
def XiGridSignBlock.check {n : ℕ} (s : XiGridSignBlock n) (c : SharedXiGridCheck) : Bool :=
  allIndices (fun i : Fin (n + 1) => c.checkSign s.sample[i.val]) &&
    allIndices (fun i : Fin n => decide
      (s.sample[i.castSucc.val].point.index < s.sample[i.succ.val].point.index ∧
        s.sample[i.castSucc.val].positive ≠ s.sample[i.succ.val].positive))

/-- Accepted samples and adjacent checks imply the original global ordered-row predicate. -/
theorem XiGridSignBlock.valid_of_check {n : ℕ} (s : XiGridSignBlock n)
    {c : SharedXiGridCheck} (hc : c.Valid) (base span : ℚ) (hs : 0 < span)
    (hb : c.model.base = (base : ℝ)) (hr : c.model.radius = rationalGridRadius span)
    (h : s.check c = true) :
    XiSignRows.Valid (s.rows base span c.rows.levels)
      (s.ordinate base span c.rows.levels 0)
      (s.ordinate base span c.rows.levels (Fin.last n)) := by
  simp only [check, Bool.and_eq_true, allIndices_eq_true, decide_eq_true_eq] at h
  apply XiSignRows.valid_of_endpoints
  · apply (rationalGridHeight_strictMono base span c.rows.levels hs).comp
    exact Fin.strictMono_iff_lt_succ.mpr (fun i => (h.2 i).1)
  · intro i
    exact (XiSignRow.valid_of_checked_sign_grid hc base span hs hb hr
      s.sample[i.castSucc.val] s.sample[i.succ.val]
      (h.1 i.castSucc) (h.1 i.succ) (h.2 i).1 (h.2 i).2).2

/-- Check only the first and last ordinates against the enclosing block endpoints. -/
def XiGridSignBlock.checkPlacement {n : ℕ} (s : XiGridSignBlock n) (base span : ℚ)
    (levels : ℕ) (A B : ℚ) : Bool :=
  decide (A ≤ s.ordinate base span levels 0 ∧ s.ordinate base span levels (Fin.last n) ≤ B)

/-- Checked placement and signs give an ordered block on the requested interval. -/
theorem XiGridSignBlock.valid_on_of_checks {n : ℕ} (s : XiGridSignBlock n)
    {c : SharedXiGridCheck} (hc : c.Valid) (base span : ℚ) (hs : 0 < span)
    (hb : c.model.base = (base : ℝ)) (hr : c.model.radius = rationalGridRadius span)
    (h : s.check c = true) {A B : ℚ}
    (hplace : s.checkPlacement base span c.rows.levels A B = true) :
    XiSignRows.Valid (s.rows base span c.rows.levels) A B := by
  simp only [checkPlacement, decide_eq_true_eq] at hplace
  exact (s.valid_of_check hc base span hs hb hr h).enlarge hplace.1 hplace.2

/-- A checked shard exports only its count and placement, independent of a later Turing window. -/
theorem XiGridSignBlock.countSummary_of_checks {n : ℕ} (s : XiGridSignBlock n)
    {c : SharedXiGridCheck} (hc : c.Valid) (base span : ℚ) (hs : 0 < span)
    (hb : c.model.base = (base : ℝ)) (hr : c.model.radius = rationalGridRadius span)
    (h : s.check c = true) {A B : ℚ}
    (hplace : s.checkPlacement base span c.rows.levels A B = true) :
    XiSignRows.CountSummary n A B :=
  (s.valid_on_of_checks hc base span hs hb hr h hplace).countSummary

/-- An overshoot shard additionally exports a checked lower bound for its endpoint area. -/
theorem XiGridSignBlock.areaSummary_of_checks {n : ℕ} (s : XiGridSignBlock n)
    {c : SharedXiGridCheck} (hc : c.Valid) (base span : ℚ) (hs : 0 < span)
    (hb : c.model.base = (base : ℝ)) (hr : c.model.radius = rationalGridRadius span)
    (h : s.check c = true) {A B a b area : ℚ}
    (hplace : s.checkPlacement base span c.rows.levels A B = true)
    (harea : decide (area ≤ XiSignRows.completedAreaRat
      (s.rows base span c.rows.levels) a b) = true) :
    XiSignRows.AreaSummary n A B a b area :=
  (s.valid_on_of_checks hc base span hs hb hr h hplace).areaSummary (of_decide_eq_true harea)

/-- All sample, placement and Turing checks together certify actual low-height completeness. -/
theorem XiGridSignBlock.low_criticalLine_of_checks {n : ℕ} (s : XiGridSignBlock n)
    {c : SharedXiGridCheck} (hc : c.Valid) (base span : ℚ) (hs : 0 < span)
    (hb : c.model.base = (base : ℝ)) (hr : c.model.radius = rationalGridRadius span)
    (h : s.check c = true) {a b : ℚ}
    (hplace : s.checkPlacement base span c.rows.levels 0 b = true)
    {d : TuringMarginIntervals} (hd : d.Valid)
    (hmargin : d.check c.scalar a b
      (XiSignRows.completedAreaRat (s.rows base span c.rows.levels) a b) = true) :
    ∀ p ∈ xiLowHeightIndices (a : ℝ), (riemannXiDivisorZeroValue p).re = 1 / 2 :=
  TuringMarginIntervals.low_criticalLine_of_check hd hc.scalar
    (s.valid_on_of_checks hc base span hs hb hr h hplace) hmargin

end PrimeFactorUnimodality
