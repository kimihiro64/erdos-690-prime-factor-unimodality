import PrimeFactorUnimodality.Helpers.Analytic.AffineXiGridSigns

/-! # Affine sample checks retain exact heights, ordered coverage and completeness -/

set_option autoImplicit false

namespace PrimeFactorUnimodality.Tests

open Fourier

/-- The legacy margin branch accepts an actual phase proof without the old phase Boolean. -/
example {c : SharedXiGridCheck} (hc : c.Valid) (s : XiGridSignData)
    (hpoint : s.point.check c.rows.levels c.endpoint c.scalar c.pi c.base c.radius
      c.coefficients = true)
    (hphase : |turingCountingPhase (s.point.toGridPoint.height c.grid) - (s.phase : ℝ)| ≤
      1 / 10 + (s.phaseError : ℝ))
    (htail : checkEulerRemainder c.endpoint (ZetaCorrectionIntervals.critical (c.height s.point))
      c.model.order c.bernoulliCap s.risingCap s.tailCap = true)
    (hmargin : s.checkMargin c.rows c.model.degree c.scalar c.pi c.errors.cap = true) :
    if s.positive then 0 < xiCriticalLineValue (s.point.toGridPoint.height c.grid)
    else xiCriticalLineValue (s.point.toGridPoint.height c.grid) < 0 := by
  apply SharedXiGridCheck.sign_of_phase_bound hc s hpoint hphase htail
  simp only [XiGridSignData.checkSignMargin, Bool.or_eq_true]
  exact Or.inr (Or.inr hmargin)

example {c : SharedXiGridCheck} (hc : c.Valid) {d : XiAffinePhaseIntervals} (hd : d.Valid)
    (s : XiGridSignData) (h : c.checkAffineSign d s = true) :
    if s.positive then 0 < xiCriticalLineValue (s.point.toGridPoint.height c.grid)
    else xiCriticalLineValue (s.point.toGridPoint.height c.grid) < 0 :=
  SharedXiGridCheck.sign_of_affine_check hc hd s h

example {c : SharedXiGridCheck} (hc : c.Valid) {d : XiAffinePhaseIntervals} (hd : d.Valid)
    (base span : ℚ) (hs : 0 < span) (hb : c.model.base = (base : ℝ))
    (hr : c.model.radius = rationalGridRadius span) (p q : XiGridSignData)
    (hp : c.checkAffineSign d p = true) (hq : c.checkAffineSign d q = true)
    (hij : p.point.index < q.point.index) (ho : p.positive ≠ q.positive) :
    (rationalGridSignRow base span c.rows.levels p.point.index q.point.index).Valid :=
  XiSignRow.valid_of_affine_grid hc hd base span hs hb hr p q hp hq hij ho

example {n : ℕ} (s : XiGridSignBlock n) {c : SharedXiGridCheck} (hc : c.Valid)
    {d : XiAffinePhaseIntervals} (hd : d.Valid) (base span : ℚ) (hs : 0 < span)
    (hb : c.model.base = (base : ℝ)) (hr : c.model.radius = rationalGridRadius span)
    (h : s.checkAffine c d = true) :
    XiSignRows.Valid (s.rows base span c.rows.levels)
      (s.ordinate base span c.rows.levels 0)
      (s.ordinate base span c.rows.levels (Fin.last n)) :=
  s.valid_of_affine_check hc hd base span hs hb hr h

example {n : ℕ} (s : XiGridSignBlock n) {c : SharedXiGridCheck} (hc : c.Valid)
    {d : XiAffinePhaseIntervals} (hd : d.Valid) (base span : ℚ) (hs : 0 < span)
    (hb : c.model.base = (base : ℝ)) (hr : c.model.radius = rationalGridRadius span)
    (h : s.checkAffine c d = true) {A B : ℚ}
    (hp : s.checkPlacement base span c.rows.levels A B = true) :
    XiSignRows.CountSummary n A B := s.countSummary_of_affine_checks hc hd base span hs hb hr h hp

example {n : ℕ} (s : XiGridSignBlock n) {c : SharedXiGridCheck} (hc : c.Valid)
    {d : XiAffinePhaseIntervals} (hd : d.Valid) (base span : ℚ) (hs : 0 < span)
    (hb : c.model.base = (base : ℝ)) (hr : c.model.radius = rationalGridRadius span)
    (h : s.checkAffine c d = true) {A B a b area : ℚ}
    (hp : s.checkPlacement base span c.rows.levels A B = true)
    (ha : decide (area ≤ XiSignRows.completedAreaRat
      (s.rows base span c.rows.levels) a b) = true) :
    XiSignRows.AreaSummary n A B a b area :=
  s.areaSummary_of_affine_checks hc hd base span hs hb hr h hp ha

example {n : ℕ} (s : XiGridSignBlock n) (c : SharedXiGridCheck) (d : XiAffinePhaseIntervals)
    {p : PackedXiGridMargins (n + 1)} (hp : p.Valid (fun i => s.sample[i.val]) c)
    (hm : p.check = true) (hi : s.checkAffineInputs c d = true) : s.checkAffine c d = true :=
  s.checkAffine_of_packedMargins c d hp hm hi

example {n : ℕ} (s : XiGridSignBlock n) {c : SharedXiGridCheck} (hc : c.Valid)
    {d : XiAffinePhaseIntervals} (hd : d.Valid) (base span : ℚ) (hs : 0 < span)
    (hb : c.model.base = (base : ℝ)) (hr : c.model.radius = rationalGridRadius span)
    {p : PackedXiGridMargins (n + 1)} (hp : p.Valid (fun i => s.sample[i.val]) c)
    (hm : p.check = true) (hi : s.checkAffineInputs c d = true) {A B : ℚ}
    (hplace : s.checkPlacement base span c.rows.levels A B = true) :
    XiSignRows.CountSummary n A B :=
  s.countSummary_of_affine_checks hc hd base span hs hb hr
    (s.checkAffine_of_packedMargins c d hp hm hi) hplace

example {n : ℕ} (s : XiGridSignBlock n) {c : SharedXiGridCheck} (hc : c.Valid)
    {d : XiAffinePhaseIntervals} (hd : d.Valid) (base span : ℚ) (hs : 0 < span)
    (hb : c.model.base = (base : ℝ)) (hr : c.model.radius = rationalGridRadius span)
    (h : s.checkAffine c d = true) {a b : ℚ}
    (hp : s.checkPlacement base span c.rows.levels 0 b = true)
    {m : TuringMarginIntervals} (hm : m.Valid)
    (hmargin : m.check c.scalar a b
      (XiSignRows.completedAreaRat (s.rows base span c.rows.levels) a b) = true) :
    ∀ p ∈ xiLowHeightIndices (a : ℝ), (riemannXiDivisorZeroValue p).re = 1 / 2 :=
  s.low_criticalLine_of_affine_checks hc hd base span hs hb hr h hp hm hmargin

example {n : ℕ} (s : XiGridSignBlock n) {c : SharedXiGridCheck} (hc : c.Valid)
    {d : XiAffinePhaseIntervals} (hd : d.Valid) (base span : ℚ) (hs : 0 < span)
    (hb : c.model.base = (base : ℝ)) (hr : c.model.radius = rationalGridRadius span)
    {p : PackedXiGridMargins (n + 1)} (hp : p.Valid (fun i => s.sample[i.val]) c)
    (hm : p.check = true) (hi : s.checkAffineInputs c d = true) {a b : ℚ}
    (hplace : s.checkPlacement base span c.rows.levels 0 b = true)
    {m : TuringMarginIntervals} (hvalid : m.Valid)
    (hmargin : m.check c.scalar a b
      (XiSignRows.completedAreaRat (s.rows base span c.rows.levels) a b) = true) :
    ∀ q ∈ xiLowHeightIndices (a : ℝ), (riemannXiDivisorZeroValue q).re = 1 / 2 :=
  s.low_criticalLine_of_affine_checks hc hd base span hs hb hr
    (s.checkAffine_of_packedMargins c d hp hm hi) hplace hvalid hmargin

def affineStoredSign (index : ℤ) (positive : Bool) : XiGridSignData :=
  ⟨⟨index, 0, ⟨0, 0⟩, 0⟩, 0, 0, 0, 1, 1, 0, positive⟩

example (c : SharedXiGridCheck) (d : XiAffinePhaseIntervals) :
    (XiGridSignBlock.mk #v[affineStoredSign 1 true, affineStoredSign 0 false]).checkAffine c d =
      false := by
  simp [XiGridSignBlock.checkAffine, allIndices, affineStoredSign]

example (c : SharedXiGridCheck) (d : XiAffinePhaseIntervals) :
    (XiGridSignBlock.mk #v[affineStoredSign 0 true, affineStoredSign 1 true]).checkAffine c d =
      false := by
  simp [XiGridSignBlock.checkAffine, allIndices, affineStoredSign]

example (c : SharedXiGridCheck) (d : XiAffinePhaseIntervals) :
    (XiGridSignBlock.mk #v[affineStoredSign 0 true, affineStoredSign 0 false]).checkAffineInputs
      c d = false := by
  simp [XiGridSignBlock.checkAffineInputs, allIndices, affineStoredSign]

end PrimeFactorUnimodality.Tests
