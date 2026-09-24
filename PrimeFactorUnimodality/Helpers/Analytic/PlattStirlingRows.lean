import PrimeFactorUnimodality.Helpers.Analytic.GammaStirlingRational
import PrimeFactorUnimodality.Helpers.Analytic.PlattStirlingKernel

/-! # Compact data interface for compensated Gamma samples

The order, window and common normalization enclosure are stored once.
Each row stores only its elementary-function approximations, error budgets
and one base output. Higher kernel orders reuse that output. These are
semantic validity obligations, not an assertion that any rows have been checked.
-/

namespace PrimeFactorUnimodality

open Complex

/-- Shared data for a complete family of Gamma-window input rows. -/
structure PlattStirlingContext where
  order : ℕ
  center : ℚ
  width : ℚ
  logTwoPi : ℚ
  logTwoPiError : ℚ
  deriving DecidableEq, Repr

/-- Elementary input enclosures and one rounded exponential output for a sample. -/
structure PlattStirlingRow where
  ell : ℚ
  theta : ℚ
  shift : ℚ
  ellError : ℚ
  thetaError : ℚ
  shiftError : ℚ
  expError : ℚ
  argumentCap : ℚ
  value : RationalPoint
  deriving DecidableEq, Repr

/-- The exact rational Gamma argument at a rational offset. -/
def PlattStirlingContext.argument (c : PlattStirlingContext) (v : ℚ) : RationalPoint :=
  ⟨1 / 4, (v + c.center) / 2⟩

/-- The common analytic normalization is checked once per context. -/
def PlattStirlingContext.Valid (c : PlattStirlingContext) : Prop :=
  1 ≤ c.order ∧ |Real.log (2 * Real.pi) - (c.logTwoPi : ℝ)| ≤ (c.logTwoPiError : ℝ)

/-- Exact rational assembly of the compensated logarithmic input. -/
def PlattStirlingRow.logInput (r : PlattStirlingRow) (c : PlattStirlingContext) (v : ℚ) :
    RationalPoint :=
  (gammaStirlingRationalInput c.order (c.argument v) r.ell r.theta c.logTwoPi).add
    (RationalPoint.ofRat r.shift)

/-- One rational budget for the three elementary input errors and compensation error. -/
def PlattStirlingRow.logError (r : PlattStirlingRow) (c : PlattStirlingContext) : ℚ :=
  r.argumentCap * (r.ellError / 2 + r.thetaError) + c.logTwoPiError / 2 + r.shiftError

/-- Local soundness conditions; the argument cap uses the shared squared-norm Boolean check. -/
def PlattStirlingRow.Valid (r : PlattStirlingRow) (c : PlattStirlingContext) (v : ℚ) : Prop :=
  |Real.log (((c.argument v).re : ℝ) ^ 2 + ((c.argument v).im : ℝ) ^ 2) -
    (r.ell : ℝ)| ≤ (r.ellError : ℝ) ∧
  |Real.arctan (((c.argument v).im : ℝ) / ((c.argument v).re : ℝ)) -
    (r.theta : ℝ)| ≤ (r.thetaError : ℝ) ∧
  |plattKernelLogShift c.center c.width v - (r.shift : ℝ)| ≤ (r.shiftError : ℝ) ∧
  ‖exp (r.logInput c v).toComplex - r.value.toComplex‖ ≤ (r.expError : ℝ) ∧
  ((c.argument v).sub (RationalPoint.ofRat (1 / 2))).normLE r.argumentCap = true

/-- The stored rational argument is exactly the analytic kernel's argument. -/
theorem PlattStirlingContext.toComplex_argument (c : PlattStirlingContext) (v : ℚ) :
    (c.argument v).toComplex = plattKernelArgument c.center v := by
  apply Complex.ext <;> simp [argument, RationalPoint.toComplex, plattKernelArgument]

/-- Ordered chunk coverage uses the same indexed data and offset function throughout. -/
def PlattStirlingRow.ValidRange (c : PlattStirlingContext) (offset : ℕ → ℚ)
    (rows : ℕ → PlattStirlingRow) (start size : ℕ) : Prop :=
  ∀ i, start ≤ i → i < start + size → (rows i).Valid c (offset i)

/-- Adjacent checked chunks compose without duplicating either rows or their validity proofs. -/
theorem PlattStirlingRow.ValidRange.append {c : PlattStirlingContext} {offset : ℕ → ℚ}
    {rows : ℕ → PlattStirlingRow} {start m n : ℕ}
    (hm : ValidRange c offset rows start m) (hn : ValidRange c offset rows (start + m) n) :
    ValidRange c offset rows start (m + n) := by
  intro i hi hi'
  by_cases h : i < start + m
  · exact hm i hi h
  · exact hn i (by omega) (by omega)

/-- The empty chunk is valid at every boundary. -/
theorem PlattStirlingRow.validRange_zero (c : PlattStirlingContext) (offset : ℕ → ℚ)
    (rows : ℕ → PlattStirlingRow) (start : ℕ) : ValidRange c offset rows start 0 := by
  intro i hi hi'
  omega

end PrimeFactorUnimodality
