import PrimeFactorUnimodality.Helpers.Analytic.ZetaGroupedEvaluation
import PrimeFactorUnimodality.Mathlib.Analysis.Fourier.GroupedGrid

/-! # Shared Fourier blocks and inexpensive per-grid-point data

The moment block and one trace per Taylor order are checked once. Each
sample supplies only its signed grid index and short Euler correction.
All arithmetic and transcendental errors remain explicit.
-/

namespace PrimeFactorUnimodality

noncomputable section

open Complex Finset Fourier ZMod

/-- Shared moment data and a single transformed array for each Taylor order. -/
structure ZetaGridBlock where
  shared : ZetaGroupedBlock
  levels : ℕ
  trace : ℕ → RadixTrace levels

/-- The shared moments and every required transform are verified once per block. -/
def ZetaGridBlock.Valid (d : ZetaGridBlock) : Prop :=
  d.shared.Valid ∧ ∀ j ∈ range d.shared.degree,
    (d.trace j).Valid (stdAddChar (1 : ZMod (2 ^ d.levels)))
      (aliasVector d.levels d.shared.groups (fun b => d.shared.coefficient b j))

/-- A signed grid index and the short correction suffice at each sample. -/
structure ZetaGridPoint where
  index : ℤ
  correction : ℂ
  correctionError : ℝ

/-- Normalized coordinate; negative indices use the same shared transform arrays. -/
def ZetaGridPoint.coordinate (p : ZetaGridPoint) (d : ZetaGridBlock) : ℝ :=
  2 * Real.pi * p.index / (2 ^ d.levels)

/-- The actual height on the critical line. -/
def ZetaGridPoint.height (p : ZetaGridPoint) (d : ZetaGridBlock) : ℝ :=
  d.shared.base + d.shared.radius * p.coordinate d

/-- Exact phases provide the already-proved grouped evaluator as an intermediate identity. -/
def ZetaGridPoint.asGrouped (p : ZetaGridPoint) (d : ZetaGridBlock) : ZetaGroupedPoint :=
  ⟨p.coordinate d, fun b => exp (I * ((p.coordinate d * b : ℝ) : ℂ)), fun _ => 0,
    p.correction, p.correctionError⟩

/-- Per-point checks exclude both the long prefix and the shared Fourier work. -/
def ZetaGridPoint.Valid (p : ZetaGridPoint) (d : ZetaGridBlock) : Prop :=
  |p.coordinate d| ≤ 1 ∧
    ‖zetaEulerCorrection d.shared.cutoff ((1 / 2 : ℂ) + p.height d * I) d.shared.order -
      p.correction‖ ≤ p.correctionError

/-- Array lookup followed by a short polynomial evaluation gives the approximate zeta value. -/
def ZetaGridPoint.value (p : ZetaGridPoint) (d : ZetaGridBlock) : ℂ :=
  (∑ j ∈ range d.shared.degree,
    (d.trace j).values[(p.index : ZMod (2 ^ d.levels)).val]'(val_lt _) *
      (p.coordinate d : ℂ) ^ j) + p.correction

/-- Every transformed-moment error is weighted by its actual evaluation power. -/
def ZetaGridPoint.transformError (p : ZetaGridPoint) (d : ZetaGridBlock) : ℝ :=
  ∑ j ∈ range d.shared.degree, (d.trace j).error * |p.coordinate d| ^ j

/-- Complete Euler, moment, correction and Fourier-computation error. -/
def ZetaGridPoint.error (p : ZetaGridPoint) (d : ZetaGridBlock) : ℝ :=
  (p.asGrouped d).error d.shared + p.transformError d

/-- A checked grid point satisfies the existing exact-phase grouped interface. -/
theorem ZetaGridPoint.Valid.asGrouped {p : ZetaGridPoint} {d : ZetaGridBlock}
    (hp : p.Valid d) : (p.asGrouped d).Valid d.shared := by
  refine ⟨hp.1, ?_, hp.2⟩
  intro b hb
  simp [ZetaGridPoint.asGrouped]

end

end PrimeFactorUnimodality
