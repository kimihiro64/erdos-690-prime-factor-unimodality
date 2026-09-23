import PrimeFactorUnimodality.Helpers.Analytic.ZetaEulerApproximation
import PrimeFactorUnimodality.Mathlib.NumberTheory.LSeries.GroupedEvaluation

/-! # Shared block data and per-point rounding for zeta evaluation

The large Dirichlet prefix is represented by one family of frequency-group
moments, reusable throughout a real height window. Each sample supplies only
group phases and the short Euler correction. Every approximation error is
explicit; neither zero signs nor completeness are fields of the shared data.
-/

namespace PrimeFactorUnimodality

noncomputable section

open Complex Finset Polynomial

/-- The short endpoint and Bernoulli part of the existing arbitrary-order Euler formula. -/
def zetaEulerCorrection (N : ℕ) (s : ℂ) (m : ℕ) : ℂ :=
  (-N ^ (1 - s)) / (1 - s) + (-N ^ (-s)) / 2 +
    ∑ j ∈ range m, (bernoulliNormalizedReal (j + 2) 0 : ℂ) * zetaRisingFactor s (j + 1) *
      (N : ℂ) ^ (-s - ((j + 1 : ℕ) : ℂ))

/-- The zero index contributes nothing, leaving precisely the positive Dirichlet prefix. -/
theorem zetaEulerApproxOrder_eq_prefix_add_correction (N m : ℕ) {s : ℂ} (hs : s ≠ 0) :
    zetaEulerApproxOrder N s m =
      (∑ n ∈ Icc 1 N, 1 / (n : ℂ) ^ s) + zetaEulerCorrection N s m := by
  have hset : range (N + 1) = insert 0 (Icc 1 N) := by
    ext n
    simp only [mem_range, mem_insert, mem_Icc]
    omega
  unfold zetaEulerApproxOrder zetaEulerApprox zetaEulerCorrection
  rw [hset, sum_insert (by simp)]
  simp only [Nat.cast_zero, zero_cpow hs, div_zero, zero_add]
  ring

/-- Base height, cutoff and moments are shared by all samples in one block. -/
structure ZetaGroupedBlock where
  cutoff : ℕ
  order : ℕ
  degree : ℕ
  base : ℝ
  radius : ℝ
  groups : Finset ℤ
  bin : ℕ → ℤ
  coefficient : ℤ → ℕ → ℂ
  coefficientError : ℤ → ℕ → ℝ

/-- The exact center on the critical line. -/
def ZetaGroupedBlock.center (d : ZetaGroupedBlock) : ℂ := (1 / 2 : ℂ) + d.base * I

/-- Only finite moment enclosures and frequency placement require shared numerical verification. -/
structure ZetaGroupedBlock.Valid (d : ZetaGroupedBlock) : Prop where
  cutoff_pos : 0 < d.cutoff
  covers : ∀ n ∈ Icc 1 d.cutoff, d.bin n ∈ d.groups
  residual : ∀ n ∈ Icc 1 d.cutoff,
    |dirichletFrequency d.radius n - (d.bin n : ℝ)| ≤ (1 / 2 : ℝ)
  moments : ∀ b ∈ d.groups, ∀ j ∈ range d.degree,
    ‖expSumMoment ((Icc 1 d.cutoff).filter (fun n => d.bin n = b))
      (fun n => 1 / (n : ℂ) ^ d.center) (fun n => dirichletFrequency d.radius n - b) j -
        d.coefficient b j‖ ≤ d.coefficientError b j

/-- Per-point data consists of phases and the short Euler correction, not another long prefix. -/
structure ZetaGroupedPoint where
  coordinate : ℝ
  phase : ℤ → ℂ
  phaseError : ℤ → ℝ
  correction : ℂ
  correctionError : ℝ

/-- The actual height represented by a normalized block coordinate. -/
def ZetaGroupedPoint.height (p : ZetaGroupedPoint) (d : ZetaGroupedBlock) : ℝ :=
  d.base + d.radius * p.coordinate

/-- The rounded finite value obtained using the shared coefficient family. -/
def ZetaGroupedPoint.value (p : ZetaGroupedPoint) (d : ZetaGroupedBlock) : ℂ :=
  (∑ b ∈ d.groups, p.phase b *
    ∑ j ∈ range d.degree, d.coefficient b j * (p.coordinate : ℂ) ^ j) + p.correction

/-- A sample certifies its small phase/correction computations inside the shared unit window. -/
structure ZetaGroupedPoint.Valid (p : ZetaGroupedPoint) (d : ZetaGroupedBlock) : Prop where
  window : |p.coordinate| ≤ 1
  phases : ∀ b ∈ d.groups,
    ‖exp (I * ((p.coordinate * b : ℝ) : ℂ)) - p.phase b‖ ≤ p.phaseError b
  correction : ‖zetaEulerCorrection d.cutoff ((1 / 2 : ℂ) + p.height d * I) d.order -
    p.correction‖ ≤ p.correctionError

/-- Truncation, stored-coefficient, phase and short-correction errors are all retained. -/
def ZetaGroupedPoint.roundingBudget (p : ZetaGroupedPoint) (d : ZetaGroupedBlock) : ℝ :=
  (d.cutoff : ℝ) * ((1 / 2 : ℝ) ^ d.degree * Real.exp (1 / 2)) +
    (∑ b ∈ d.groups, ((∑ j ∈ range d.degree, d.coefficientError b j * |p.coordinate| ^ j) +
      ‖∑ j ∈ range d.degree, d.coefficient b j * (p.coordinate : ℂ) ^ j‖ * p.phaseError b)) +
    p.correctionError

/-- The complete Euler remainder is added to every finite-evaluation error. -/
def ZetaGroupedPoint.error (p : ZetaGroupedPoint) (d : ZetaGroupedBlock) : ℝ :=
  zetaEulerError d.cutoff ((1 / 2 : ℂ) + p.height d * I) d.order + p.roundingBudget d

end

end PrimeFactorUnimodality
