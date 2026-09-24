import PrimeFactorUnimodality.Helpers.Analytic.GammaStirlingExpansion
import PrimeFactorUnimodality.Mathlib.Analysis.Complex.RationalPoint

/-! # Exact rational assembly of finite Stirling corrections

At a rational complex argument, every Bernoulli correction is rational
complex arithmetic. A single recursive evaluator and induction cover all
orders and inputs; no emitted proof branch per sample is needed.
-/

namespace PrimeFactorUnimodality

open Complex Polynomial

/-- The rational coefficient of the next reciprocal power. -/
def gammaStirlingCoefficient (j : ℕ) : ℚ :=
  (j.factorial : ℚ) * (_root_.bernoulli (j + 2) / ((j + 2).factorial : ℚ))

/-- Horner assembly computes each power implicitly, with one multiplication per coefficient. -/
def gammaStirlingHorner : ℕ → ℕ → RationalPoint → RationalPoint
  | 0, _, _ => RationalPoint.ofRat 0
  | n + 1, j, w => w.mul
      ((RationalPoint.ofRat (gammaStirlingCoefficient j)).add (gammaStirlingHorner n (j + 1) w))

/-- The shared Horner computation evaluates the exact finite power sum. -/
theorem toComplex_gammaStirlingHorner (n j : ℕ) (w : RationalPoint) :
    (gammaStirlingHorner n j w).toComplex =
      ∑ r ∈ Finset.range n, (gammaStirlingCoefficient (j + r) : ℂ) * w.toComplex ^ (r + 1) := by
  induction n generalizing j with
  | zero => simp [gammaStirlingHorner]
  | succ n ih =>
    rw [gammaStirlingHorner, RationalPoint.toComplex_mul, RationalPoint.toComplex_add,
      RationalPoint.toComplex_ofRat, ih, Finset.sum_range_succ']
    simp only [Nat.add_zero]
    rw [mul_add, Finset.mul_sum]
    have hs : (∑ r ∈ Finset.range n,
        w.toComplex * ((gammaStirlingCoefficient (j + 1 + r) : ℂ) *
          w.toComplex ^ (r + 1))) =
        ∑ r ∈ Finset.range n, (gammaStirlingCoefficient (j + (r + 1)) : ℂ) *
          w.toComplex ^ (r + 1 + 1) := by
      apply Finset.sum_congr rfl
      intro r _
      rw [show j + 1 + r = j + (r + 1) by omega, pow_succ]
      ring
    rw [hs]
    ring

/-- One inverse and a linear Horner pass evaluate the finite rational correction. -/
def gammaStirlingRationalCorrection (M : ℕ) (z : RationalPoint) : RationalPoint :=
  gammaStirlingHorner M 0 z.inv

/-- The reusable rational evaluator is exactly the analytic correction at every order. -/
theorem toComplex_gammaStirlingRationalCorrection (M : ℕ) (z : RationalPoint) :
    (gammaStirlingRationalCorrection M z).toComplex = gammaStirlingCorrection M z.toComplex := by
  rw [gammaStirlingRationalCorrection, toComplex_gammaStirlingHorner]
  simp only [Nat.zero_add, RationalPoint.toComplex_inv, gammaStirlingCorrection]
  apply Finset.sum_congr rfl
  intro j _
  rw [bernoulliNormalizedReal_zero, gammaStirlingCoefficient]
  push_cast
  ring

/-- Assemble an approximate normalized logarithm using only rational complex arithmetic. -/
def gammaStirlingRationalInput (M : ℕ) (z : RationalPoint) (ell theta c : ℚ) : RationalPoint :=
  ((((z.sub (RationalPoint.ofRat (1 / 2))).mul ⟨ell / 2, theta⟩).sub z).add
    (RationalPoint.ofRat (c / 2))).add (gammaStirlingRationalCorrection M z)

/-- Exact meaning of the input, with only three approximate real-function values. -/
theorem toComplex_gammaStirlingRationalInput (M : ℕ) (z : RationalPoint) (ell theta c : ℚ) :
    (gammaStirlingRationalInput M z ell theta c).toComplex =
      (z.toComplex - 1 / 2) * (((ell / 2 : ℚ) : ℂ) + (theta : ℂ) * I) - z.toComplex +
        ((c / 2 : ℚ) : ℂ) + gammaStirlingCorrection M z.toComplex := by
  have he : (RationalPoint.toComplex ⟨ell / 2, theta⟩) =
      ((ell / 2 : ℚ) : ℂ) + (theta : ℂ) * I := by
    apply Complex.ext <;> simp [RationalPoint.toComplex]
  simp only [gammaStirlingRationalInput, RationalPoint.toComplex_add,
    RationalPoint.toComplex_sub, RationalPoint.toComplex_mul, RationalPoint.toComplex_ofRat,
    toComplex_gammaStirlingRationalCorrection, he]
  push_cast
  rfl

end PrimeFactorUnimodality
