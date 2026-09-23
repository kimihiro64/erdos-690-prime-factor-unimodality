import PrimeFactorUnimodality.Helpers.Analytic.DirichletAtomIntervals
import PrimeFactorUnimodality.Helpers.Analytic.MomentIntervalColumns

/-! # Compact consecutive-index moment chunks

A chunk stores only its starting index, length, common frequency bin and
integer phase shifts. Evaluation materializes each atom once, reuses its
moment recurrence, and assembles all column enclosures. The soundness theorem
refers to the actual finite complex Dirichlet moments, not supplied numerical
error hypotheses. Consecutive chunks can subsequently share certified sums.
-/

namespace PrimeFactorUnimodality

open Complex LeanCert.Core Finset

/-- A bounded consecutive group of atoms with one shared integer frequency bin. -/
structure MomentIntervalChunk where
  first : ℕ
  count : ℕ
  group : ℤ
  turns : Vector ℤ count

/-- One shared evaluation result for all residual and coefficient checks. -/
structure MomentChunkEvaluation (degree : ℕ) where
  residuals : Bool
  columns : Vector ComplexInterval degree

/-- Both rational endpoints must lie in the full permitted residual window. -/
def residualWithinHalf (R : IntervalRat) : Bool :=
  decide (-(1 / 2 : ℚ) ≤ R.lo ∧ R.hi ≤ (1 / 2 : ℚ))

/-- The residual test proves the actual half-unit bound, including both endpoints. -/
theorem abs_le_half_of_residualWithinHalf {R : IntervalRat}
    (h : residualWithinHalf R = true) {x : ℝ} (hx : x ∈ R) : |x| ≤ (1 / 2 : ℝ) := by
  simp only [residualWithinHalf, decide_eq_true_eq] at h
  have hlo : ((-(1 / 2 : ℚ) : ℚ) : ℝ) ≤ (R.lo : ℝ) := Rat.cast_le.mpr h.1
  have hhi : (R.hi : ℝ) ≤ ((1 / 2 : ℚ) : ℝ) := Rat.cast_le.mpr h.2
  norm_num only [Rat.cast_neg, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat] at hlo hhi
  exact abs_le.mpr ⟨hlo.trans hx.1, hx.2.trans hhi⟩

namespace MomentIntervalChunk

/-- A bounded array lookup selects the proposed period shift; every integer choice is sound. -/
def atom (r : MomentIntervalChunk) (c : SharedTaylorIntervals) (P : IntervalRat)
    (base radius : ℚ) (n : ℕ) : DirichletAtomInterval :=
  dirichletAtomInterval c P base radius n r.group
    (r.turns.toArray[n - r.first]?.getD 0)

/-- Compute the shared atoms and their columns once, before checking any rounded coefficients. -/
def evaluate (r : MomentIntervalChunk) (c : SharedTaylorIntervals) (P : IntervalRat)
    (base radius : ℚ) (degree : ℕ) : MomentChunkEvaluation degree :=
  let atoms := (List.range' r.first r.count).map (r.atom c P base radius)
  ⟨atoms.all (fun a => residualWithinHalf a.residual),
    ComplexInterval.sumVectors (atoms.map
      (fun a => ComplexInterval.momentVector a.weight a.residual degree))⟩

/-- Evaluation encloses every exact moment on the complete consecutive index set. -/
theorem evaluate_mem (r : MomentIntervalChunk) {c : SharedTaylorIntervals} (hc : c.Prepared)
    {P : IntervalRat} (hpi : Real.pi ∈ P) (base radius : ℚ) (degree : ℕ)
    (hfirst : 0 < r.first) (j : Fin degree) :
    expSumMoment (Ico r.first (r.first + r.count))
      (fun n => 1 / (n : ℂ) ^ ((1 / 2 : ℂ) + (base : ℂ) * I))
      (fun n => -(radius : ℝ) * Real.log n - r.group) j.val ∈
        (r.evaluate c P base radius degree).columns[j.val] := by
  let value (n : ℕ) : ℂ := (1 / (n : ℂ) ^ ((1 / 2 : ℂ) + (base : ℂ) * I)) *
    (I * ((-(radius : ℝ) * Real.log n - r.group : ℝ) : ℂ)) ^ j.val /
      (j.val.factorial : ℂ)
  have hsum := ComplexInterval.sumVectors_sound (List.range' r.first r.count) value
    (fun n => let a := r.atom c P base radius n
      ComplexInterval.momentVector a.weight a.residual degree) j (by
      intro n hn
      have hn₀ : 0 < n := by
        obtain ⟨i, hi, rfl⟩ := List.mem_range'.mp hn
        omega
      have ha := dirichletAtomInterval_sound hc hpi base radius n hn₀ r.group
        (r.turns.toArray[n - r.first]?.getD 0)
      exact ComplexInterval.momentVector_sound _ _ degree ha.1 ha.2 j)
  have hset : (List.range' r.first r.count).toFinset = Ico r.first (r.first + r.count) := by
    ext n
    simp
  have he : expSumMoment (Ico r.first (r.first + r.count))
      (fun n => 1 / (n : ℂ) ^ ((1 / 2 : ℂ) + (base : ℂ) * I))
      (fun n => -(radius : ℝ) * Real.log n - r.group) j.val =
      ((List.range' r.first r.count).map value).sum := by
    rw [expSumMoment, ← hset, List.sum_toFinset _ (List.nodup_range' ..)]
  rw [he]
  simpa only [evaluate, List.map_map, Function.comp_def] using hsum

/-- The shared residual check covers every index of the chunk, not just its endpoints. -/
theorem evaluate_residuals (r : MomentIntervalChunk) {c : SharedTaylorIntervals}
    (hc : c.Prepared) {P : IntervalRat} (hpi : Real.pi ∈ P)
    (base radius : ℚ) (degree : ℕ) (hfirst : 0 < r.first)
    (h : (r.evaluate c P base radius degree).residuals = true)
    {n : ℕ} (hn : n ∈ Ico r.first (r.first + r.count)) :
    |-(radius : ℝ) * Real.log n - r.group| ≤ (1 / 2 : ℝ) := by
  have hnlist : n ∈ List.range' r.first r.count := by simpa using hn
  have ha := dirichletAtomInterval_sound hc hpi base radius n
    (hfirst.trans_le (mem_Ico.mp hn).1) r.group (r.turns.toArray[n - r.first]?.getD 0)
  have hcheck : residualWithinHalf (r.atom c P base radius n).residual = true := by
    exact List.all_eq_true.mp h _ (List.mem_map.mpr ⟨n, hnlist, rfl⟩)
  exact abs_le_half_of_residualWithinHalf hcheck ha.2

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
