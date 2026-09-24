import PrimeFactorUnimodality.Helpers.Analytic.CheckedXiGridRows
import PrimeFactorUnimodality.Helpers.Arithmetic.PackedStrictBounds

/-! # Packed strict margins feed the existing xi-sign and Turing consumers

Two packed comparisons discharge a block's phase guards and oriented value
margins. The enclosure predicate must be proved from the actual grid data;
it is never an unchecked assertion in the integer certificate. Point, phase,
Euler, ordering, placement and Turing obligations are all retained.
-/

namespace PrimeFactorUnimodality

open Fourier LeanCert.Core

/-- Packed comparison rows for the phase and zeta margins of exactly `n` samples. -/
structure PackedXiGridMargins (n : ℕ) where
  phase : PackedStrictBounds n
  value : PackedStrictBounds n

/-- Both full packed comparisons are checked once for the block. -/
def PackedXiGridMargins.check {n : ℕ} (p : PackedXiGridMargins n) : Bool :=
  p.phase.check && p.value.check

/-- All bridges concern actual grid intervals and full errors, with both sign orientations. -/
structure PackedXiGridMargins.Valid {n : ℕ} (p : PackedXiGridMargins n)
    (sample : Fin n → XiGridSignData) (c : SharedXiGridCheck) : Prop where
  phase_nonneg : ∀ i, 0 ≤ (sample i).phaseError
  phase : p.phase.Encloses (fun i => (sample i).cardinalPhaseBudget c.pi) (fun _ => c.pi.lo / 2)
  value : p.value.Encloses (fun i => (sample i).projectionBudget c.errors.cap)
    (fun i => if (sample i).positive then
      ((sample i).cardinalProjection c.rows c.model.degree c.pi).lo
    else -((sample i).cardinalProjection c.rows c.model.degree c.pi).hi)

/-- Bulk inequalities discharge each original cardinal margin without scalar replay. -/
theorem PackedXiGridMargins.margins_of_check {n : ℕ} {p : PackedXiGridMargins n}
    {sample : Fin n → XiGridSignData} {c : SharedXiGridCheck}
    (hp : p.Valid sample c) (h : p.check = true) (i : Fin n) :
    (sample i).checkCardinalMargin c.rows c.model.degree c.pi c.errors.cap = true := by
  simp only [check, Bool.and_eq_true] at h
  have hphase := PackedStrictBounds.lt_of_encloses_check hp.phase h.1 i
  have hvalue := PackedStrictBounds.lt_of_encloses_check hp.value h.2 i
  simp only [XiGridSignData.checkCardinalMargin, decide_eq_true_eq]
  refine ⟨hp.phase_nonneg i, hphase, ?_⟩
  cases hs : (sample i).positive with
  | true => simpa only [hs, ↓reduceIte] using hvalue
  | false =>
    simp only [hs, Bool.false_eq_true, ↓reduceIte] at hvalue ⊢
    linarith

/-- Non-margin sample obligations and adjacent order remain executable checks. -/
def XiGridSignBlock.checkInputs {n : ℕ} (s : XiGridSignBlock n) (c : SharedXiGridCheck) : Bool :=
  allIndices (fun i : Fin (n + 1) =>
    let t := s.sample[i.val]
    t.point.check c.rows.levels c.endpoint c.scalar c.pi c.base c.radius c.coefficients &&
      c.phaseData.check c.scalar (c.height t.point) t.phase t.phaseError &&
      checkEulerRemainder c.endpoint (ZetaCorrectionIntervals.critical (c.height t.point))
        c.model.order c.bernoulliCap t.risingCap t.tailCap) &&
    allIndices (fun i : Fin n => decide
      (s.sample[i.castSucc.val].point.index < s.sample[i.succ.val].point.index ∧
        s.sample[i.castSucc.val].positive ≠ s.sample[i.succ.val].positive))

/-- Packed margins and retained input checks imply the original full block Boolean. -/
theorem XiGridSignBlock.check_of_packedMargins {n : ℕ} (s : XiGridSignBlock n)
    (c : SharedXiGridCheck) {p : PackedXiGridMargins (n + 1)}
    (hp : p.Valid (fun i => s.sample[i.val]) c)
    (hm : p.check = true) (hi : s.checkInputs c = true) : s.check c = true := by
  simp only [checkInputs, Bool.and_eq_true, allIndices_eq_true] at hi
  simp only [XiGridSignBlock.check, Bool.and_eq_true, allIndices_eq_true]
  refine ⟨fun i => ?_, hi.2⟩
  simp only [SharedXiGridCheck.checkSign, Bool.and_eq_true, Bool.or_eq_true]
  exact ⟨hi.1 i, Or.inl (p.margins_of_check hp hm i)⟩

/-- The packed route concludes the same actual low-height completeness theorem. -/
theorem XiGridSignBlock.low_criticalLine_of_packedChecks {n : ℕ} (s : XiGridSignBlock n)
    {c : SharedXiGridCheck} (hc : c.Valid) (base span : ℚ) (hs : 0 < span)
    (hb : c.model.base = (base : ℝ)) (hr : c.model.radius = rationalGridRadius span)
    {p : PackedXiGridMargins (n + 1)} (hp : p.Valid (fun i => s.sample[i.val]) c)
    (hm : p.check = true) (hi : s.checkInputs c = true) {a b : ℚ}
    (hplace : s.checkPlacement base span c.rows.levels 0 b = true)
    {d : TuringMarginIntervals} (hd : d.Valid)
    (hmargin : d.check c.scalar a b
      (XiSignRows.completedAreaRat (s.rows base span c.rows.levels) a b) = true) :
    ∀ q ∈ xiLowHeightIndices (a : ℝ), (riemannXiDivisorZeroValue q).re = 1 / 2 :=
  s.low_criticalLine_of_checks hc base span hs hb hr
    (s.check_of_packedMargins c hp hm hi) hplace hd hmargin

end PrimeFactorUnimodality
