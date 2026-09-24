import PrimeFactorUnimodality.Helpers.Analytic.TuringMarginIntervals

/-! # Stable complete Turing-budget regression cases -/

set_option autoImplicit false

namespace PrimeFactorUnimodality.Tests

noncomputable section

open LeanCert.Core TuringMarginIntervals

example {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    xiZeroCountingMainIntegral b - xiZeroCountingMainIntegral a =
      ((b ^ 2 - a ^ 2) * (Real.log a - Real.log (2 * Real.pi) - 3 / 2) +
        b ^ 2 * Real.log (b / a)) / (4 * Real.pi) := by
  exact PrimeFactorUnimodality.xiZeroCountingMainIntegral_sub_eq_stable ha hb

example {c : SharedTaylorIntervals} (hc : c.Prepared)
    (P : IntervalRat.IntervalRatNonzero) (hP : 0 < P.lo) (hpi : Real.pi ∈ P.toIntervalRat) :
    (prepare c P).Valid := by
  exact PrimeFactorUnimodality.TuringMarginIntervals.prepare_valid hc P hP hpi

example {d : TuringMarginIntervals} (hd : d.Valid)
    {c : SharedTaylorIntervals} (hc : c.Prepared) {a b : ℚ} (ha : 0 < a) (hb : 0 < b) :
    (((b : ℝ) ^ 2 - (a : ℝ) ^ 2) * (Real.log a - Real.log (2 * Real.pi) - 3 / 2) +
      (b : ℝ) ^ 2 * Real.log ((b : ℝ) / (a : ℝ))) ∈ d.differenceNumerator c a b := by
  exact PrimeFactorUnimodality.TuringMarginIntervals.mem_differenceNumerator hd hc ha hb

example {d : TuringMarginIntervals} (hd : d.Valid)
    {c : SharedTaylorIntervals} (hc : c.Prepared) {a b : ℚ} (ha : 0 < a) (hb : 0 < b) :
    xiZeroCountingMainIntegral b - xiZeroCountingMainIntegral a +
      turingCountErrorBudget a b ∈ d.completeBudget c a b := by
  exact PrimeFactorUnimodality.TuringMarginIntervals.mem_completeBudget hd hc ha hb

example {d : TuringMarginIntervals} (hd : d.Valid)
    {c : SharedTaylorIntervals} (hc : c.Prepared) {a b area : ℚ}
    (h : d.check c a b area = true) :
    32 ≤ a ∧ a ≤ b ∧ xiZeroCountingMainIntegral b - xiZeroCountingMainIntegral a +
      turingCountErrorBudget a b < (b : ℝ) - a + area := by
  exact PrimeFactorUnimodality.TuringMarginIntervals.margin_of_check hd hc h

example {d : TuringMarginIntervals} (hd : d.Valid)
    {c : SharedTaylorIntervals} (hc : c.Prepared) {n : ℕ} {rows : Fin n → XiSignRow}
    {a b : ℚ} (hrows : XiSignRows.Valid rows 0 b)
    (h : d.check c a b (XiSignRows.completedAreaRat rows a b) = true) :
    ∀ p ∈ xiLowHeightIndices (a : ℝ), (riemannXiDivisorZeroValue p).re = 1 / 2 := by
  exact PrimeFactorUnimodality.TuringMarginIntervals.low_criticalLine_of_check hd hc hrows h

example {d : TuringMarginIntervals} (hd : d.Valid) {c : SharedTaylorIntervals} (hc : c.Prepared)
    {n : ℕ} {a b area : ℚ} (hs : XiSignRows.AreaSummary n 0 b a b area)
    (h : d.check c a b area = true) :
    ∀ p ∈ xiLowHeightIndices (a : ℝ), (riemannXiDivisorZeroValue p).re = 1 / 2 :=
  TuringMarginIntervals.low_criticalLine_of_summary hd hc hs h

example {d : TuringMarginIntervals} (hd : d.Valid) {c : SharedTaylorIntervals} (hc : c.Prepared)
    {n m : ℕ} {a b area : ℚ} (hs : XiSignRows.CountSummary n 0 a)
    (ht : XiSignRows.AreaSummary m a b a b area)
    (h : d.check c a b ((n : ℚ) * (b - a) + area) = true) :
    ∀ p ∈ xiLowHeightIndices (a : ℝ), (riemannXiDivisorZeroValue p).re = 1 / 2 :=
  TuringMarginIntervals.low_criticalLine_of_summary hd hc
    ((hs.area_before le_rfl).append ht) h


def coarsePi : IntervalRat.IntervalRatNonzero :=
  ⟨⟨3, 4, by norm_num⟩, by norm_num [IntervalRat.containsZero]⟩
def marginConstants : TuringMarginIntervals :=
  TuringMarginIntervals.prepare (SharedTaylorIntervals.prepare 0) coarsePi

example : marginConstants.Valid := by
  apply TuringMarginIntervals.prepare_valid (SharedTaylorIntervals.prepare_prepared 0)
    coarsePi (by norm_num [coarsePi])
  exact ⟨Real.pi_gt_three.le, Real.pi_lt_four.le⟩

example : marginConstants.check (SharedTaylorIntervals.prepare 0) 32 32 1000 = true :=
  by decide +kernel
example : marginConstants.check (SharedTaylorIntervals.prepare 0) 32 32 0 = false :=
  by decide +kernel
example : marginConstants.check (SharedTaylorIntervals.prepare 0) 0 32 1000 = false :=
  by decide +kernel
example : marginConstants.check (SharedTaylorIntervals.prepare 0) 32 31 1000 = false :=
  by decide +kernel
example : marginConstants.differenceNumerator (SharedTaylorIntervals.prepare 0) 32 32 =
    IntervalRat.singleton 0 := by decide +kernel

example {d : TuringMarginIntervals} (hd : d.Valid) {c : SharedTaylorIntervals} (hc : c.Prepared)
    (h : d.check c 32 33 1000 = true) :
    xiZeroCountingMainIntegral 33 - xiZeroCountingMainIntegral 32 +
      turingCountErrorBudget 32 33 < 1001 := by
  have hm := TuringMarginIntervals.margin_of_check hd hc h
  norm_num at hm
  exact hm

end

end PrimeFactorUnimodality.Tests
