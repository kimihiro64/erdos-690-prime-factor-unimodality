import PrimeFactorUnimodality.Helpers.Analytic.DusartBoxExplicitFormula

/-! # The exact box-cutoff range, smoothness, and endpoint regressions -/

namespace PrimeFactorUnimodality.Tests

open Real Set

example (m : ℕ) {h : ℝ} (hh : 0 < h) : ContDiff ℝ 2 (dusartBoxDistribution m h) :=
  contDiff_dusartBoxDistribution m hh

example (m : ℕ) {h : ℝ} (hh : 0 < h) (t : ℝ) :
    dusartBoxDistribution m h t ∈ Icc (0 : ℝ) 1 := dusartBoxDistribution_mem_Icc m hh t

example (m : ℕ) {h : ℝ} (hh : 0 < h) : dusartBoxDistribution m h 0 = 1 :=
  dusartBoxDistribution_eq_one m hh le_rfl

example (m : ℕ) {h : ℝ} (hh : 0 < h) :
    dusartBoxDistribution m h (-((m + 3 : ℕ) : ℝ) * h) = 0 := by
  apply dusartBoxDistribution_eq_zero m hh
  linarith

example (m : ℕ) {h : ℝ} (hh : 0 < h) (x : ℝ) : ContDiff ℝ 2 (dusartBoxWeight m h x) :=
  contDiff_dusartBoxWeight m hh x

example (m : ℕ) {h x : ℝ} (hh : 0 < h) (hx : 1 ≤ x) : dusartBoxWeight m h x 0 = 1 :=
  dusartBoxWeight_zero m hh hx

example (m : ℕ) {h x : ℝ} (hh : 0 < h) (hx : 1 < x) : 0 < dusartBoxSupport m h x :=
  dusartBoxSupport_pos m hh hx

example (m : ℕ) {h x : ℝ} (hh : 0 < h) (hx : 0 < x) :
    dusartBoxWeight m h x (dusartBoxSupport m h x) = 0 :=
  dusartBoxWeight_eq_zero m hh hx le_rfl

example (m : ℕ) {h x : ℝ} (hh : 0 < h) (hx : 1 ≤ x) :
    deriv (dusartBoxWeight m h x) 0 = 0 := deriv_dusartBoxWeight_zero m hh hx

example (m : ℕ) {h x : ℝ} (hh : 0 < h) (hx : 0 < x) :
    deriv (dusartBoxWeight m h x) (dusartBoxSupport m h x) = 0 :=
  deriv_dusartBoxWeight_support m hh hx

end PrimeFactorUnimodality.Tests
