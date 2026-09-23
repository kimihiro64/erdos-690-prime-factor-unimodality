import PrimeFactorUnimodality.Helpers.Analytic.CheckedXiGridRows

/-! # Checked shared endpoints, ordering and placement regressions -/

set_option autoImplicit false

namespace PrimeFactorUnimodality.Tests

noncomputable section

open Fourier

example {n : ℕ} (s : XiGridSignBlock n)
    {c : SharedXiGridCheck} (hc : c.Valid) (base span : ℚ) (hs : 0 < span)
    (hb : c.model.base = (base : ℝ)) (hr : c.model.radius = rationalGridRadius span)
    (h : s.check c = true) :
    XiSignRows.Valid (s.rows base span c.rows.levels)
      (s.ordinate base span c.rows.levels 0)
      (s.ordinate base span c.rows.levels (Fin.last n)) := by
  exact PrimeFactorUnimodality.XiGridSignBlock.valid_of_check s hc base span hs hb hr h

example {n : ℕ} {rows : Fin n → XiSignRow} {a b A B : ℚ}
    (h : XiSignRows.Valid rows a b) (ha : A ≤ a) (hb : b ≤ B) :
    XiSignRows.Valid rows A B := by
  exact PrimeFactorUnimodality.XiSignRows.Valid.enlarge h ha hb

example {n : ℕ} (s : XiGridSignBlock n)
    {c : SharedXiGridCheck} (hc : c.Valid) (base span : ℚ) (hs : 0 < span)
    (hb : c.model.base = (base : ℝ)) (hr : c.model.radius = rationalGridRadius span)
    (h : s.check c = true) {A B : ℚ}
    (hplace : s.checkPlacement base span c.rows.levels A B = true) :
    XiSignRows.Valid (s.rows base span c.rows.levels) A B := by
  exact PrimeFactorUnimodality.XiGridSignBlock.valid_on_of_checks s hc base span hs hb hr h hplace

example {n : ℕ} (s : XiGridSignBlock n)
    {c : SharedXiGridCheck} (hc : c.Valid) (base span : ℚ) (hs : 0 < span)
    (hb : c.model.base = (base : ℝ)) (hr : c.model.radius = rationalGridRadius span)
    (h : s.check c = true) {a b : ℚ}
    (hplace : s.checkPlacement base span c.rows.levels 0 b = true)
    {d : TuringMarginIntervals} (hd : d.Valid)
    (hmargin : d.check c.scalar a b
      (XiSignRows.completedAreaRat (s.rows base span c.rows.levels) a b) = true) :
    ∀ p ∈ xiLowHeightIndices (a : ℝ), (riemannXiDivisorZeroValue p).re = 1 / 2 := by
  exact PrimeFactorUnimodality.XiGridSignBlock.low_criticalLine_of_checks s hc base span hs hb hr h hplace hd hmargin


def storedSign (index : ℤ) (positive : Bool) : XiGridSignData :=
  ⟨⟨index, 0, ⟨0, 0⟩, 0⟩, 0, 0, 0, 1, 1, 0, positive⟩
def sharedBlock : XiGridSignBlock 2 :=
  ⟨#v[storedSign (-2) true, storedSign 0 false, storedSign 3 true]⟩

example : sharedBlock.ordinate 100 8 3 0 = 98 := by decide +kernel
example : (sharedBlock.rows 100 8 3 0).upper =
    (sharedBlock.rows 100 8 3 1).lower := rfl
example : sharedBlock.checkPlacement 100 8 3 98 103 = true := by decide +kernel
example : sharedBlock.checkPlacement 100 8 3 99 103 = false := by decide +kernel
example : sharedBlock.checkPlacement 100 8 3 98 102 = false := by decide +kernel
example (c : SharedXiGridCheck) :
    (XiGridSignBlock.mk #v[storedSign 1 true, storedSign 0 false]).check c = false := by
  simp [XiGridSignBlock.check, allIndices, storedSign]
example (c : SharedXiGridCheck) :
    (XiGridSignBlock.mk #v[storedSign 0 true, storedSign 1 true]).check c = false := by
  simp [XiGridSignBlock.check, allIndices, storedSign]
example {n m : ℕ} {rows : Fin n → XiSignRow} {next : Fin m → XiSignRow}
    {a b c : ℚ} (h : XiSignRows.Valid rows a b) (hn : XiSignRows.Valid next b c) :
    XiSignRows.Valid (Fin.append rows next) a c := h.append hn

end

end PrimeFactorUnimodality.Tests
