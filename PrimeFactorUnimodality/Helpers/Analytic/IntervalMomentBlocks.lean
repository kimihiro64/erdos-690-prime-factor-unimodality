import PrimeFactorUnimodality.Helpers.Analytic.DirichletMomentBlocks
import PrimeFactorUnimodality.Helpers.Analytic.IntervalMomentChunks

/-! # Real-parameter moment checks feed the existing reusable blocks

The same retained block, rounding, concatenation and full-grid partition
proofs apply without alteration. Only the local atom builder now accepts
proved real enclosures for the base height and radius.
-/

namespace PrimeFactorUnimodality.DirichletMomentBlock

open Complex LeanCert.Core

/-- Checked real enclosures supply every field of the existing retained-block predicate. -/
theorem valid_of_interval_check (r : MomentIntervalChunk) {c : SharedTaylorIntervals}
    (hc : c.Prepared) {P B R : IntervalRat} (hpi : Real.pi ∈ P)
    {base radius : ℝ} (hb : base ∈ B) (hr : radius ∈ R) {degree : ℕ}
    (coefficients : Vector RationalPoint degree) (errors : Vector ℚ degree)
    (h : r.checkIntervals c P B R coefficients errors = true) :
    (ofChunk r coefficients errors).Valid base radius := by
  have h' := h
  simp only [MomentIntervalChunk.checkIntervals, Bool.and_eq_true, decide_eq_true_eq] at h'
  refine ⟨h'.1.1, Nat.le_add_right _ _, ?_, ?_⟩
  · intro n hn
    exact r.evaluateIntervals_residuals hc hpi hb hr degree h'.1.1 h'.1.2 hn
  · intro j
    exact r.checkIntervals_moments hc hpi hb hr coefficients errors h j

end PrimeFactorUnimodality.DirichletMomentBlock
