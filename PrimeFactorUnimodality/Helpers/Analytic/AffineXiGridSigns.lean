import PrimeFactorUnimodality.Helpers.Analytic.PackedXiGridMargins
import PrimeFactorUnimodality.Helpers.Analytic.XiAffinePhaseIntervals

/-! # Shared affine phases feed actual grid signs and Turing summaries

The only replaced sample operation is phase evaluation. Point validity,
Euler tails, all sign-margin alternatives, strict ordering and placement
are retained. The same soundness theorem handles both the old and affine
phase checkers. Packed margins can still discharge their comparisons in
bulk; no old per-sample logarithm check is inferred from the new Boolean.
-/

namespace PrimeFactorUnimodality

open Fourier

/-- Use a shared affine phase model while preserving all other sample checks. -/
def SharedXiGridCheck.checkAffineSign (c : SharedXiGridCheck) (d : XiAffinePhaseIntervals)
    (s : XiGridSignData) : Bool :=
  s.point.check c.rows.levels c.endpoint c.scalar c.pi c.base c.radius c.coefficients &&
    d.check (c.height s.point) s.phase s.phaseError &&
    checkEulerRemainder c.endpoint (ZetaCorrectionIntervals.critical (c.height s.point))
      c.model.order c.bernoulliCap s.risingCap s.tailCap &&
    (s.checkCardinalMargin c.rows c.model.degree c.pi c.errors.cap ||
      s.checkSignMargin c.rows c.model.degree c.scalar c.pi c.errors.cap)

/-- A checked affine phase supplies the actual counting-phase premise of the common sign proof. -/
theorem SharedXiGridCheck.sign_of_affine_check {c : SharedXiGridCheck} (hc : c.Valid)
    {d : XiAffinePhaseIntervals} (hd : d.Valid) (s : XiGridSignData)
    (h : c.checkAffineSign d s = true) :
    if s.positive then 0 < xiCriticalLineValue (s.point.toGridPoint.height c.grid)
    else xiCriticalLineValue (s.point.toGridPoint.height c.grid) < 0 := by
  simp only [checkAffineSign, Bool.and_eq_true] at h
  exact sign_of_phase_bound hc s h.1.1.1
    (XiAffinePhaseIntervals.abs_counting_sub_le_of_check hd (mem_height hc s.point) h.1.1.2)
    h.1.2 h.2

/-- Adjacent affine-checked signs certify the unchanged exact rational sign interval. -/
theorem XiSignRow.valid_of_affine_grid {c : SharedXiGridCheck} (hc : c.Valid)
    {d : XiAffinePhaseIntervals} (hd : d.Valid)
    (base span : ℚ) (hs : 0 < span) (hb : c.model.base = (base : ℝ))
    (hr : c.model.radius = rationalGridRadius span) (p q : XiGridSignData)
    (hp : c.checkAffineSign d p = true) (hq : c.checkAffineSign d q = true)
    (hij : p.point.index < q.point.index) (hopposite : p.positive ≠ q.positive) :
    (rationalGridSignRow base span c.rows.levels p.point.index q.point.index).Valid :=
  valid_of_grid_signs c base span hs hb hr p q
    (SharedXiGridCheck.sign_of_affine_check hc hd p hp)
    (SharedXiGridCheck.sign_of_affine_check hc hd q hq) hij hopposite

/-- Samples share one affine model and only adjacent order/orientation checks. -/
def XiGridSignBlock.checkAffine {n : ℕ} (s : XiGridSignBlock n) (c : SharedXiGridCheck)
    (d : XiAffinePhaseIntervals) : Bool :=
  allIndices (fun i : Fin (n + 1) => c.checkAffineSign d s.sample[i.val]) &&
    allIndices (fun i : Fin n => decide
      (s.sample[i.castSucc.val].point.index < s.sample[i.succ.val].point.index ∧
        s.sample[i.castSucc.val].positive ≠ s.sample[i.succ.val].positive))

/-- Affine sample checking preserves the original globally ordered-row predicate. -/
theorem XiGridSignBlock.valid_of_affine_check {n : ℕ} (s : XiGridSignBlock n)
    {c : SharedXiGridCheck} (hc : c.Valid) {d : XiAffinePhaseIntervals} (hd : d.Valid)
    (base span : ℚ) (hs : 0 < span) (hb : c.model.base = (base : ℝ))
    (hr : c.model.radius = rationalGridRadius span) (h : s.checkAffine c d = true) :
    XiSignRows.Valid (s.rows base span c.rows.levels)
      (s.ordinate base span c.rows.levels 0)
      (s.ordinate base span c.rows.levels (Fin.last n)) := by
  simp only [checkAffine, Bool.and_eq_true, allIndices_eq_true, decide_eq_true_eq] at h
  apply XiSignRows.valid_of_endpoints
  · apply (rationalGridHeight_strictMono base span c.rows.levels hs).comp
    exact Fin.strictMono_iff_lt_succ.mpr (fun i => (h.2 i).1)
  · intro i
    exact (XiSignRow.valid_of_affine_grid hc hd base span hs hb hr
      s.sample[i.castSucc.val] s.sample[i.succ.val]
      (h.1 i.castSucc) (h.1 i.succ) (h.2 i).1 (h.2 i).2).2

/-- The existing endpoint placement check gives a checked block on the requested interval. -/
theorem XiGridSignBlock.valid_on_of_affine_checks {n : ℕ} (s : XiGridSignBlock n)
    {c : SharedXiGridCheck} (hc : c.Valid) {d : XiAffinePhaseIntervals} (hd : d.Valid)
    (base span : ℚ) (hs : 0 < span) (hb : c.model.base = (base : ℝ))
    (hr : c.model.radius = rationalGridRadius span) (h : s.checkAffine c d = true)
    {A B : ℚ} (hp : s.checkPlacement base span c.rows.levels A B = true) :
    XiSignRows.Valid (s.rows base span c.rows.levels) A B := by
  simp only [checkPlacement, decide_eq_true_eq] at hp
  exact (s.valid_of_affine_check hc hd base span hs hb hr h).enlarge hp.1 hp.2

/-- Prefix shards retain just counts and placement for every later Turing integration window. -/
theorem XiGridSignBlock.countSummary_of_affine_checks {n : ℕ} (s : XiGridSignBlock n)
    {c : SharedXiGridCheck} (hc : c.Valid) {d : XiAffinePhaseIntervals} (hd : d.Valid)
    (base span : ℚ) (hs : 0 < span) (hb : c.model.base = (base : ℝ))
    (hr : c.model.radius = rationalGridRadius span) (h : s.checkAffine c d = true)
    {A B : ℚ} (hp : s.checkPlacement base span c.rows.levels A B = true) :
    XiSignRows.CountSummary n A B :=
  (s.valid_on_of_affine_checks hc hd base span hs hb hr h hp).countSummary

/-- Overshoot shards retain a proved scalar completed-area lower bound. -/
theorem XiGridSignBlock.areaSummary_of_affine_checks {n : ℕ} (s : XiGridSignBlock n)
    {c : SharedXiGridCheck} (hc : c.Valid) {d : XiAffinePhaseIntervals} (hd : d.Valid)
    (base span : ℚ) (hs : 0 < span) (hb : c.model.base = (base : ℝ))
    (hr : c.model.radius = rationalGridRadius span) (h : s.checkAffine c d = true)
    {A B a b area : ℚ} (hp : s.checkPlacement base span c.rows.levels A B = true)
    (ha : decide (area ≤ XiSignRows.completedAreaRat
      (s.rows base span c.rows.levels) a b) = true) :
    XiSignRows.AreaSummary n A B a b area :=
  (s.valid_on_of_affine_checks hc hd base span hs hb hr h hp).areaSummary (of_decide_eq_true ha)

/-- Retain all non-margin obligations when the two margin families are checked in bulk. -/
def XiGridSignBlock.checkAffineInputs {n : ℕ} (s : XiGridSignBlock n) (c : SharedXiGridCheck)
    (d : XiAffinePhaseIntervals) : Bool :=
  allIndices (fun i : Fin (n + 1) =>
    let t := s.sample[i.val]
    t.point.check c.rows.levels c.endpoint c.scalar c.pi c.base c.radius c.coefficients &&
      d.check (c.height t.point) t.phase t.phaseError &&
      checkEulerRemainder c.endpoint (ZetaCorrectionIntervals.critical (c.height t.point))
        c.model.order c.bernoulliCap t.risingCap t.tailCap) &&
    allIndices (fun i : Fin n => decide
      (s.sample[i.castSucc.val].point.index < s.sample[i.succ.val].point.index ∧
        s.sample[i.castSucc.val].positive ≠ s.sample[i.succ.val].positive))

/-- Packed margin proofs and affine input checks imply the complete new block Boolean. -/
theorem XiGridSignBlock.checkAffine_of_packedMargins {n : ℕ} (s : XiGridSignBlock n)
    (c : SharedXiGridCheck) (d : XiAffinePhaseIntervals) {p : PackedXiGridMargins (n + 1)}
    (hp : p.Valid (fun i => s.sample[i.val]) c) (hm : p.check = true)
    (hi : s.checkAffineInputs c d = true) : s.checkAffine c d = true := by
  simp only [checkAffineInputs, Bool.and_eq_true, allIndices_eq_true] at hi
  simp only [checkAffine, Bool.and_eq_true, allIndices_eq_true]
  refine ⟨fun i => ?_, hi.2⟩
  simp only [SharedXiGridCheck.checkAffineSign, Bool.and_eq_true, Bool.or_eq_true]
  exact ⟨hi.1 i, Or.inl (p.margins_of_check hp hm i)⟩

/-- The full affine route reaches the same actual low-height completeness statement. -/
theorem XiGridSignBlock.low_criticalLine_of_affine_checks {n : ℕ} (s : XiGridSignBlock n)
    {c : SharedXiGridCheck} (hc : c.Valid) {d : XiAffinePhaseIntervals} (hd : d.Valid)
    (base span : ℚ) (hs : 0 < span) (hb : c.model.base = (base : ℝ))
    (hr : c.model.radius = rationalGridRadius span) (h : s.checkAffine c d = true)
    {a b : ℚ} (hp : s.checkPlacement base span c.rows.levels 0 b = true)
    {m : TuringMarginIntervals} (hm : m.Valid)
    (hmargin : m.check c.scalar a b
      (XiSignRows.completedAreaRat (s.rows base span c.rows.levels) a b) = true) :
    ∀ p ∈ xiLowHeightIndices (a : ℝ), (riemannXiDivisorZeroValue p).re = 1 / 2 :=
  TuringMarginIntervals.low_criticalLine_of_check hm hc.scalar
    (s.valid_on_of_affine_checks hc hd base span hs hb hr h hp) hmargin

end PrimeFactorUnimodality
