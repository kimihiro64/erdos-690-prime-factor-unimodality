import PrimeFactorUnimodality.Helpers.Analytic.SharedLogIntervals
import PrimeFactorUnimodality.Helpers.Analytic.XiTuringVerification

/-! # Checked scalar margins for actual Turing completeness

An exact rearrangement shares the large endpoint terms before enclosing
them. In particular, the logarithm of `2*pi` is charged only to `b^2-a^2`,
not to two independent squares. Rational interval arithmetic retains the
entire main integral and the proved counting-error budget. Accepted strict
margins feed the existing sign-row completeness theorem.
-/

namespace PrimeFactorUnimodality

open LeanCert.Core

/-- An exact endpoint difference with one shared large logarithmic contribution. -/
theorem xiZeroCountingMainIntegral_sub_eq_stable {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    xiZeroCountingMainIntegral b - xiZeroCountingMainIntegral a =
      ((b ^ 2 - a ^ 2) * (Real.log a - Real.log (2 * Real.pi) - 3 / 2) +
        b ^ 2 * Real.log (b / a)) / (4 * Real.pi) := by
  have hp : (2 * Real.pi) ≠ 0 := by positivity
  unfold xiZeroCountingMainIntegral
  rw [Real.log_div hb.ne' hp, Real.log_div ha.ne' hp, Real.log_div hb.ne' ha.ne']
  field_simp
  ring

/-- Shared pi and logarithm enclosures for an entire collection of Turing margins. -/
structure TuringMarginIntervals where
  pi : IntervalRat.IntervalRatNonzero
  logTwoPi : IntervalRat

/-- The constants enclose the actual pi and logarithm, not rounded substitutes. -/
def TuringMarginIntervals.Valid (d : TuringMarginIntervals) : Prop :=
  Real.pi ∈ d.pi.toIntervalRat ∧ Real.log (2 * Real.pi) ∈ d.logTwoPi

/-- Prepare the shared logarithm once from a nonzero pi interval. -/
def TuringMarginIntervals.prepare (c : SharedTaylorIntervals) (P : IntervalRat.IntervalRatNonzero) :
    TuringMarginIntervals :=
  ⟨P, c.logInterval (IntervalRat.scale 2 P.toIntervalRat)⟩

/-- A positive pi enclosure and prepared scalar evaluator validate the constants. -/
theorem TuringMarginIntervals.prepare_valid {c : SharedTaylorIntervals} (hc : c.Prepared)
    (P : IntervalRat.IntervalRatNonzero) (hP : 0 < P.lo) (hpi : Real.pi ∈ P.toIntervalRat) :
    (prepare c P).Valid := by
  refine ⟨hpi, ?_⟩
  apply SharedTaylorIntervals.mem_logInterval hc
  · norm_num [IntervalRat.scale]
    exact hP
  · simpa using IntervalRat.mem_scale 2 hpi

/-- Two logarithms and the shared constant enclose the endpoint-difference numerator. -/
def TuringMarginIntervals.differenceNumerator (d : TuringMarginIntervals) (c : SharedTaylorIntervals)
    (a b : ℚ) : IntervalRat :=
  IntervalRat.add
    (IntervalRat.scale (b ^ 2 - a ^ 2)
      (IntervalRat.sub (IntervalRat.sub (c.log a) d.logTwoPi) (IntervalRat.singleton (3 / 2))))
    (IntervalRat.scale (b ^ 2) (c.log (b / a)))

/-- The stable numerator enclosure contains the exact real expression. -/
theorem TuringMarginIntervals.mem_differenceNumerator {d : TuringMarginIntervals} (hd : d.Valid)
    {c : SharedTaylorIntervals} (hc : c.Prepared) {a b : ℚ} (ha : 0 < a) (hb : 0 < b) :
    (((b : ℝ) ^ 2 - (a : ℝ) ^ 2) * (Real.log a - Real.log (2 * Real.pi) - 3 / 2) +
      (b : ℝ) ^ 2 * Real.log ((b : ℝ) / (a : ℝ))) ∈ d.differenceNumerator c a b := by
  have hlog := SharedTaylorIntervals.mem_log hc (div_pos hb ha)
  have h := IntervalRat.mem_add
    (IntervalRat.mem_scale (b ^ 2 - a ^ 2)
      (IntervalRat.mem_sub (IntervalRat.mem_sub (SharedTaylorIntervals.mem_log hc ha) hd.2)
        (IntervalRat.mem_singleton (3 / 2))))
    (IntervalRat.mem_scale (b ^ 2) hlog)
  convert h using 1 <;>
    simp only [differenceNumerator, Rat.cast_sub, Rat.cast_pow, Rat.cast_div, Rat.cast_ofNat]

/-- Retain the smooth integral, interval-width penalty and logarithmic argument budget. -/
def TuringMarginIntervals.completeBudget (d : TuringMarginIntervals) (c : SharedTaylorIntervals)
    (a b : ℚ) : IntervalRat :=
  IntervalRat.add (IntervalRat.singleton ((15 / 16) * (b - a)))
    (IntervalRat.mul (IntervalRat.invNonzero d.pi)
      (IntervalRat.add (IntervalRat.scale (1 / 4) (d.differenceNumerator c a b))
        (IntervalRat.add (IntervalRat.scale (19 / 2) (c.log (5 * b)))
          (IntervalRat.singleton 95))))

/-- All contributions to the actual integrated counting bound lie in the interval. -/
theorem TuringMarginIntervals.mem_completeBudget {d : TuringMarginIntervals} (hd : d.Valid)
    {c : SharedTaylorIntervals} (hc : c.Prepared) {a b : ℚ} (ha : 0 < a) (hb : 0 < b) :
    xiZeroCountingMainIntegral b - xiZeroCountingMainIntegral a +
      turingCountErrorBudget a b ∈ d.completeBudget c a b := by
  have h := IntervalRat.mem_add (IntervalRat.mem_singleton ((15 / 16) * (b - a)))
    (IntervalRat.mem_mul (IntervalRat.mem_invNonzero hd.1 Real.pi_ne_zero)
      (IntervalRat.mem_add
        (IntervalRat.mem_scale (1 / 4) (mem_differenceNumerator hd hc ha hb))
        (IntervalRat.mem_add
          (IntervalRat.mem_scale (19 / 2) (SharedTaylorIntervals.mem_log hc
            (mul_pos (by norm_num : (0 : ℚ) < 5) hb))) (IntervalRat.mem_singleton 95))))
  rw [xiZeroCountingMainIntegral_sub_eq_stable (by exact_mod_cast ha) (by exact_mod_cast hb),
    turingCountErrorBudget]
  unfold completeBudget
  convert h using 1
  push_cast
  ring

/-- Check the height hypotheses and a strict comparison with the completed rational area. -/
def TuringMarginIntervals.check (d : TuringMarginIntervals) (c : SharedTaylorIntervals)
    (a b area : ℚ) : Bool :=
  decide (32 ≤ a ∧ a ≤ b ∧ (d.completeBudget c a b).hi < b - a + area)

/-- The rational comparison supplies precisely the existing Turing-margin inequality. -/
theorem TuringMarginIntervals.margin_of_check {d : TuringMarginIntervals} (hd : d.Valid)
    {c : SharedTaylorIntervals} (hc : c.Prepared) {a b area : ℚ}
    (h : d.check c a b area = true) :
    32 ≤ a ∧ a ≤ b ∧ xiZeroCountingMainIntegral b - xiZeroCountingMainIntegral a +
      turingCountErrorBudget a b < (b : ℝ) - a + area := by
  simp only [check, decide_eq_true_eq] at h
  have hm := mem_completeBudget hd hc (by linarith : 0 < a) (by linarith : 0 < b)
  have hu : ((d.completeBudget c a b).hi : ℝ) < (b : ℝ) - a + area :=
    by exact_mod_cast h.2.2
  exact ⟨h.1, h.2.1, hm.2.trans_lt hu⟩

/-- A compact summary and a checked scalar margin prove completeness with multiplicities. -/
theorem TuringMarginIntervals.low_criticalLine_of_summary {d : TuringMarginIntervals} (hd : d.Valid)
    {c : SharedTaylorIntervals} (hc : c.Prepared) {n : ℕ} {a b area : ℚ}
    (hsummary : XiSignRows.AreaSummary n 0 b a b area) (h : d.check c a b area = true) :
    ∀ p ∈ xiLowHeightIndices (a : ℝ), (riemannXiDivisorZeroValue p).re = 1 / 2 := by
  have hm := margin_of_check hd hc h
  exact hsummary.low_criticalLine_of_turing_margin hm.1 hm.2.1 hm.2.2

/-- Valid sign rows and the checked scalar margin prove completeness with multiplicities. -/
theorem TuringMarginIntervals.low_criticalLine_of_check {d : TuringMarginIntervals} (hd : d.Valid)
    {c : SharedTaylorIntervals} (hc : c.Prepared) {n : ℕ} {rows : Fin n → XiSignRow}
    {a b : ℚ} (hrows : XiSignRows.Valid rows 0 b)
    (h : d.check c a b (XiSignRows.completedAreaRat rows a b) = true) :
    ∀ p ∈ xiLowHeightIndices (a : ℝ), (riemannXiDivisorZeroValue p).re = 1 / 2 :=
  low_criticalLine_of_summary hd hc (hrows.areaSummary le_rfl) h

end PrimeFactorUnimodality
