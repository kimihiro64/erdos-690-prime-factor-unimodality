import PrimeFactorUnimodality.Helpers.Analytic.MomentChunkAssembly

/-! # Compact consecutive-index moment chunks

A chunk stores only its starting index, length, common frequency bin and
integer phase shifts. Evaluation materializes each atom once, reuses its
moment recurrence, and assembles all column enclosures. The soundness theorem
refers to the actual finite complex Dirichlet moments, not supplied numerical
error hypotheses. Consecutive chunks can subsequently share certified sums.
-/

namespace PrimeFactorUnimodality

open Complex LeanCert.Core Finset

namespace MomentIntervalChunk

/-- A bounded array lookup selects the proposed period shift; every integer choice is sound. -/
def atom (r : MomentIntervalChunk) (c : SharedTaylorIntervals) (P : IntervalRat)
    (base radius : ℚ) (n : ℕ) : DirichletAtomInterval :=
  dirichletAtomInterval c P base radius n r.group
    (r.turns.toArray[n - r.first]?.getD 0)

/-- Compute the shared atoms and their columns once, before checking any rounded coefficients. -/
def evaluate (r : MomentIntervalChunk) (c : SharedTaylorIntervals) (P : IntervalRat)
    (base radius : ℚ) (degree : ℕ) : MomentChunkEvaluation degree :=
  r.evaluateAtoms degree (r.atom c P base radius)

/-- Evaluation encloses every exact moment on the complete consecutive index set. -/
theorem evaluate_mem (r : MomentIntervalChunk) {c : SharedTaylorIntervals} (hc : c.Prepared)
    {P : IntervalRat} (hpi : Real.pi ∈ P) (base radius : ℚ) (degree : ℕ)
    (hfirst : 0 < r.first) (j : Fin degree) :
    expSumMoment (Ico r.first (r.first + r.count))
      (fun n => 1 / (n : ℂ) ^ ((1 / 2 : ℂ) + (base : ℂ) * I))
      (fun n => -(radius : ℝ) * Real.log n - r.group) j.val ∈
        (r.evaluate c P base radius degree).columns[j.val] := by
  apply r.evaluateAtoms_mem degree (r.atom c P base radius) _ _ ?_ j
  intro n hn
  exact dirichletAtomInterval_sound hc hpi base radius n
    (hfirst.trans_le (mem_Ico.mp hn).1) r.group (r.turns.toArray[n - r.first]?.getD 0)

/-- The shared residual check covers every index of the chunk, not just its endpoints. -/
theorem evaluate_residuals (r : MomentIntervalChunk) {c : SharedTaylorIntervals}
    (hc : c.Prepared) {P : IntervalRat} (hpi : Real.pi ∈ P)
    (base radius : ℚ) (degree : ℕ) (hfirst : 0 < r.first)
    (h : (r.evaluate c P base radius degree).residuals = true)
    {n : ℕ} (hn : n ∈ Ico r.first (r.first + r.count)) :
    |-(radius : ℝ) * Real.log n - r.group| ≤ (1 / 2 : ℝ) := by
  apply r.evaluateAtoms_residuals degree (r.atom c P base radius) _ ?_ h hn
  intro n hn
  exact (dirichletAtomInterval_sound hc hpi base radius n
    (hfirst.trans_le (mem_Ico.mp hn).1) r.group (r.turns.toArray[n - r.first]?.getD 0)).2

/-- All rounded coefficients share the same computed atom table and column sums. -/
def check (r : MomentIntervalChunk) (c : SharedTaylorIntervals) (P : IntervalRat)
    (base radius : ℚ) {degree : ℕ} (coefficients : Vector RationalPoint degree)
    (errors : Vector ℚ degree) : Bool :=
  let result := r.evaluate c P base radius degree
  decide (0 < r.first) && result.residuals && (List.finRange degree).all
    (fun j => result.columns[j.val].close coefficients[j.val] errors[j.val])

/-- A successful finite check supplies the actual finite-moment norm bounds. -/
theorem check_moments (r : MomentIntervalChunk) {c : SharedTaylorIntervals}
    (hc : c.Prepared) {P : IntervalRat} (hpi : Real.pi ∈ P)
    (base radius : ℚ) {degree : ℕ} (coefficients : Vector RationalPoint degree)
    (errors : Vector ℚ degree) (h : r.check c P base radius coefficients errors = true)
    (j : Fin degree) :
    ‖expSumMoment (Ico r.first (r.first + r.count))
        (fun n => 1 / (n : ℂ) ^ ((1 / 2 : ℂ) + (base : ℂ) * I))
        (fun n => -(radius : ℝ) * Real.log n - r.group) j.val -
          coefficients[j.val].toComplex‖ ≤ (errors[j.val] : ℝ) := by
  simp only [check, Bool.and_eq_true, decide_eq_true_eq] at h
  have hj := List.all_eq_true.mp h.2 j (List.mem_finRange j)
  exact ComplexInterval.norm_sub_le_of_close hj
    (r.evaluate_mem hc hpi base radius degree h.1.1 j)

end MomentIntervalChunk

end PrimeFactorUnimodality
