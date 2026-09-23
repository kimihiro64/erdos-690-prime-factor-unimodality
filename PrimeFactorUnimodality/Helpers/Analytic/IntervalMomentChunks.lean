import PrimeFactorUnimodality.Helpers.Analytic.DirichletEndpointIntervals
import PrimeFactorUnimodality.Helpers.Analytic.MomentChunkAssembly

/-! # Checked moment chunks with enclosed real base and radius

Non-rational radii, including rational multiples of reciprocal pi, use the
same materialized-atom and column assembler as rational parameters. Each
atom's logarithm is computed once and shared by amplitude, phase and residual.
-/

namespace PrimeFactorUnimodality.MomentIntervalChunk

open Complex LeanCert.Core Finset

/-- Build one atom using real base/radius enclosures and a shared endpoint logarithm. -/
def intervalAtom (r : MomentIntervalChunk) (c : SharedTaylorIntervals)
    (P B R : IntervalRat) (n : ℕ) : DirichletAtomInterval :=
  let d := DirichletEndpointIntervals.prepare c n
  ⟨d.weight c P B (r.turns.toArray[n - r.first]?.getD 0),
    IntervalRat.sub (IntervalRat.scale (-1) (IntervalRat.mul R d.logarithm))
      (IntervalRat.singleton r.group)⟩

/-- Actual critical-line weights and residuals are enclosed at every allowed pair of parameters. -/
theorem intervalAtom_sound (r : MomentIntervalChunk) {c : SharedTaylorIntervals}
    (hc : c.Prepared) {P B R : IntervalRat} (hpi : Real.pi ∈ P)
    {base radius : ℝ} (hb : base ∈ B) (hr : radius ∈ R) (n : ℕ) (hn : 0 < n) :
    1 / (n : ℂ) ^ ((1 / 2 : ℂ) + base * I) ∈ (r.intervalAtom c P B R n).weight ∧
      -radius * Real.log n - r.group ∈ (r.intervalAtom c P B R n).residual := by
  have hd := DirichletEndpointIntervals.prepare_valid hc n hn
  constructor
  · exact DirichletEndpointIntervals.mem_weight hd hc hpi hb _
  · have h := IntervalRat.mem_sub
      (IntervalRat.mem_scale (-1) (IntervalRat.mem_mul hr hd.2.1))
      (IntervalRat.mem_singleton (r.group : ℚ))
    simpa [intervalAtom, DirichletEndpointIntervals.prepare, neg_mul] using h

/-- Real enclosures reuse the same atom table, column sums and residual checks. -/
def evaluateIntervals (r : MomentIntervalChunk) (c : SharedTaylorIntervals)
    (P B R : IntervalRat) (degree : ℕ) : MomentChunkEvaluation degree :=
  r.evaluateAtoms degree (r.intervalAtom c P B R)

/-- Every exact moment on the full consecutive set is enclosed, including non-rational radii. -/
theorem evaluateIntervals_mem (r : MomentIntervalChunk) {c : SharedTaylorIntervals}
    (hc : c.Prepared) {P B R : IntervalRat} (hpi : Real.pi ∈ P)
    {base radius : ℝ} (hb : base ∈ B) (hr : radius ∈ R) (degree : ℕ)
    (hfirst : 0 < r.first) (j : Fin degree) :
    expSumMoment (Ico r.first (r.first + r.count))
      (fun n => 1 / (n : ℂ) ^ ((1 / 2 : ℂ) + base * I))
      (fun n => -radius * Real.log n - r.group) j.val ∈
        (r.evaluateIntervals c P B R degree).columns[j.val] := by
  apply r.evaluateAtoms_mem degree (r.intervalAtom c P B R) _ _ ?_ j
  intro n hn
  exact r.intervalAtom_sound hc hpi hb hr n (hfirst.trans_le (mem_Ico.mp hn).1)

/-- Checked residuals cover every positive chunk index for the same real parameters. -/
theorem evaluateIntervals_residuals (r : MomentIntervalChunk) {c : SharedTaylorIntervals}
    (hc : c.Prepared) {P B R : IntervalRat} (hpi : Real.pi ∈ P)
    {base radius : ℝ} (hb : base ∈ B) (hr : radius ∈ R) (degree : ℕ)
    (hfirst : 0 < r.first) (h : (r.evaluateIntervals c P B R degree).residuals = true)
    {n : ℕ} (hn : n ∈ Ico r.first (r.first + r.count)) :
    |-radius * Real.log n - r.group| ≤ (1 / 2 : ℝ) := by
  apply r.evaluateAtoms_residuals degree (r.intervalAtom c P B R) _ ?_ h hn
  intro n hn
  exact (r.intervalAtom_sound hc hpi hb hr n (hfirst.trans_le (mem_Ico.mp hn).1)).2

/-- Every rounded coefficient is checked against one shared interval evaluation. -/
def checkIntervals (r : MomentIntervalChunk) (c : SharedTaylorIntervals)
    (P B R : IntervalRat) {degree : ℕ} (coefficients : Vector RationalPoint degree)
    (errors : Vector ℚ degree) : Bool :=
  let result := r.evaluateIntervals c P B R degree
  decide (0 < r.first) && result.residuals && (List.finRange degree).all
    (fun j => result.columns[j.val].close coefficients[j.val] errors[j.val])

/-- A successful interval-parameter check proves the actual finite-moment error. -/
theorem checkIntervals_moments (r : MomentIntervalChunk) {c : SharedTaylorIntervals}
    (hc : c.Prepared) {P B R : IntervalRat} (hpi : Real.pi ∈ P)
    {base radius : ℝ} (hb : base ∈ B) (hr : radius ∈ R) {degree : ℕ}
    (coefficients : Vector RationalPoint degree) (errors : Vector ℚ degree)
    (h : r.checkIntervals c P B R coefficients errors = true) (j : Fin degree) :
    ‖expSumMoment (Ico r.first (r.first + r.count))
        (fun n => 1 / (n : ℂ) ^ ((1 / 2 : ℂ) + base * I))
        (fun n => -radius * Real.log n - r.group) j.val -
          coefficients[j.val].toComplex‖ ≤ (errors[j.val] : ℝ) := by
  simp only [checkIntervals, Bool.and_eq_true, decide_eq_true_eq] at h
  have hj := List.all_eq_true.mp h.2 j (List.mem_finRange j)
  exact ComplexInterval.norm_sub_le_of_close hj
    (r.evaluateIntervals_mem hc hpi hb hr degree h.1.1 j)

end PrimeFactorUnimodality.MomentIntervalChunk
