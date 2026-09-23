import Mathlib.Algebra.BigOperators.Intervals
import PrimeFactorUnimodality.Helpers.Analytic.MomentChunkIntervals

/-! # Composable checked bounds for grouped Dirichlet moments

Each block keeps just a rounded coefficient vector and its complete errors.
Adjacent blocks with the same frequency bin combine without replaying their
atoms, so bounded chunks remain independently checkable and cacheable.
-/

namespace PrimeFactorUnimodality

open Complex Finset LeanCert.Core

/-- Rounded shared coefficients on a consecutive positive index interval. -/
structure DirichletMomentBlock (degree : ℕ) where
  first : ℕ
  stop : ℕ
  group : ℤ
  coefficients : Vector RationalPoint degree
  errors : Vector ℚ degree
  deriving DecidableEq

namespace DirichletMomentBlock

/-- The exact mathematical meaning of a reusable checked block. -/
structure Valid {degree : ℕ} (r : DirichletMomentBlock degree) (base radius : ℝ) : Prop where
  positive : 0 < r.first
  ordered : r.first ≤ r.stop
  residual : ∀ n ∈ Ico r.first r.stop,
    |-radius * Real.log n - r.group| ≤ (1 / 2 : ℝ)
  moments : ∀ j : Fin degree,
    ‖expSumMoment (Ico r.first r.stop)
        (fun n => 1 / (n : ℂ) ^ ((1 / 2 : ℂ) + base * I))
        (fun n => -radius * Real.log n - r.group) j.val -
          r.coefficients[j.val].toComplex‖ ≤ (r.errors[j.val] : ℝ)

/-- Compact retained output of one checked atom chunk. -/
def ofChunk (r : MomentIntervalChunk) {degree : ℕ}
    (coefficients : Vector RationalPoint degree) (errors : Vector ℚ degree) :
    DirichletMomentBlock degree :=
  ⟨r.first, r.first + r.count, r.group, coefficients, errors⟩

/-- The executable chunk check supplies every numerical hypothesis of block validity. -/
theorem valid_of_check (r : MomentIntervalChunk) {c : SharedTaylorIntervals} (hc : c.Prepared)
    {P : IntervalRat} (hpi : Real.pi ∈ P) (base radius : ℚ) {degree : ℕ}
    (coefficients : Vector RationalPoint degree) (errors : Vector ℚ degree)
    (h : r.check c P base radius coefficients errors = true) :
    (ofChunk r coefficients errors).Valid base radius := by
  have h' := h
  simp only [MomentIntervalChunk.check, Bool.and_eq_true, decide_eq_true_eq] at h'
  refine ⟨h'.1.1, Nat.le_add_right _ _, ?_, ?_⟩
  · intro n hn
    exact r.evaluate_residuals hc hpi base radius degree h'.1.1 h'.1.2 hn
  · intro j
    simpa [ofChunk] using r.check_moments hc hpi base radius coefficients errors h j

/-- Merge only the retained coefficient/error vectors; no atom calculation is repeated. -/
def append {degree : ℕ} (left right : DirichletMomentBlock degree) :
    DirichletMomentBlock degree :=
  ⟨left.first, right.stop, left.group,
    Vector.zipWith RationalPoint.add left.coefficients right.coefficients,
    Vector.zipWith (· + ·) left.errors right.errors⟩

/-- Matching interval endpoints and frequency bins give a complete compositional bound. -/
theorem Valid.append {degree : ℕ} {left right : DirichletMomentBlock degree}
    {base radius : ℝ} (hl : left.Valid base radius) (hr : right.Valid base radius)
    (hjoin : left.stop = right.first) (hgroup : left.group = right.group) :
    (left.append right).Valid base radius := by
  refine ⟨hl.positive, hl.ordered.trans (hjoin.symm ▸ hr.ordered), ?_, ?_⟩
  · intro n hn
    have hn' : left.first ≤ n ∧ n < right.stop := mem_Ico.mp hn
    by_cases hm : n < left.stop
    · exact hl.residual n (mem_Ico.mpr ⟨hn'.1, hm⟩)
    · simpa [DirichletMomentBlock.append, hgroup] using
        hr.residual n (mem_Ico.mpr ⟨by omega, hn'.2⟩)
  · intro j
    have hs : expSumMoment (Ico left.first right.stop)
        (fun n => 1 / (n : ℂ) ^ ((1 / 2 : ℂ) + base * I))
        (fun n => -radius * Real.log n - left.group) j.val =
        expSumMoment (Ico left.first left.stop)
          (fun n => 1 / (n : ℂ) ^ ((1 / 2 : ℂ) + base * I))
          (fun n => -radius * Real.log n - left.group) j.val +
        expSumMoment (Ico right.first right.stop)
          (fun n => 1 / (n : ℂ) ^ ((1 / 2 : ℂ) + base * I))
          (fun n => -radius * Real.log n - left.group) j.val := by
      simpa only [expSumMoment, hjoin] using
        (sum_Ico_consecutive (fun n =>
          (1 / (n : ℂ) ^ ((1 / 2 : ℂ) + base * I)) *
            (I * ((-radius * Real.log n - left.group : ℝ) : ℂ)) ^ j.val /
              (j.val.factorial : ℂ)) hl.ordered (hjoin.symm ▸ hr.ordered)).symm
    have hright := hr.moments j
    rw [← hgroup] at hright
    simp only [DirichletMomentBlock.append, Vector.getElem_zipWith,
      RationalPoint.toComplex_add, Rat.cast_add]
    rw [hs, add_sub_add_comm]
    exact (norm_add_le _ _).trans (add_le_add (hl.moments j) hright)

/-- Replace retained values by short rational checkpoints, preserving the interval and bin. -/
def rounded {degree : ℕ} (r : DirichletMomentBlock degree)
    (coefficients : Vector RationalPoint degree) (errors : Vector ℚ degree) :
    DirichletMomentBlock degree := {r with coefficients, errors}

/-- Only the increment in each error budget is available for checkpoint rounding. -/
def checkRounding {degree : ℕ} (r : DirichletMomentBlock degree)
    (coefficients : Vector RationalPoint degree) (errors : Vector ℚ degree) : Bool :=
  (List.finRange degree).all (fun j =>
    (r.coefficients[j.val].sub coefficients[j.val]).normLE (errors[j.val] - r.errors[j.val]))

/-- Checked outward rounding bounds rational growth without replaying the underlying atoms. -/
theorem Valid.rounded {degree : ℕ} {r : DirichletMomentBlock degree} {base radius : ℝ}
    (hr : r.Valid base radius) (coefficients : Vector RationalPoint degree)
    (errors : Vector ℚ degree) (h : r.checkRounding coefficients errors = true) :
    (r.rounded coefficients errors).Valid base radius := by
  refine ⟨hr.positive, hr.ordered, hr.residual, ?_⟩
  intro j
  have hj := List.all_eq_true.mp h j (List.mem_finRange j)
  have hdiff := (RationalPoint.normLE_eq_true _ _).mp hj
  simp only [RationalPoint.toComplex_sub, Rat.cast_sub] at hdiff
  have htriangle := norm_sub_le_norm_sub_add_norm_sub
    (expSumMoment (Ico r.first r.stop)
      (fun n => 1 / (n : ℂ) ^ ((1 / 2 : ℂ) + base * I))
      (fun n => -radius * Real.log n - r.group) j.val)
    r.coefficients[j.val].toComplex coefficients[j.val].toComplex
  have hbound := hr.moments j
  change ‖expSumMoment (Ico r.first r.stop)
    (fun n => 1 / (n : ℂ) ^ ((1 / 2 : ℂ) + base * I))
    (fun n => -radius * Real.log n - r.group) j.val -
      coefficients[j.val].toComplex‖ ≤ (errors[j.val] : ℝ)
  linarith

end DirichletMomentBlock

end PrimeFactorUnimodality
