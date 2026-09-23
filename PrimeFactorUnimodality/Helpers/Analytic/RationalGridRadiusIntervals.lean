import LeanCert.Core.IntervalRat.Basic
import PrimeFactorUnimodality.Helpers.Analytic.RationalGridHeights

/-! # Rational interval enclosures for exact rational-height grid radii

The reciprocal pi interval encloses `span/(2*pi)`. This same real-radius
enclosure can be reused by moment, sample correction and phase checkers.
-/

namespace PrimeFactorUnimodality

open LeanCert.Core

/-- Scale a checked reciprocal-pi interval by half the rational grid span. -/
def rationalGridRadiusInterval (P : IntervalRat.IntervalRatNonzero) (span : ℚ) : IntervalRat :=
  IntervalRat.scale (span / 2) (IntervalRat.invNonzero P)

/-- The real grid radius lies in the computed enclosure, including signed spans. -/
theorem mem_rationalGridRadiusInterval (P : IntervalRat.IntervalRatNonzero)
    (hpi : Real.pi ∈ P.toIntervalRat) (span : ℚ) :
    rationalGridRadius span ∈ rationalGridRadiusInterval P span := by
  have h := IntervalRat.mem_scale (span / 2) (IntervalRat.mem_invNonzero hpi Real.pi_ne_zero)
  simpa [rationalGridRadius, rationalGridRadiusInterval, div_eq_mul_inv, mul_assoc,
    mul_left_comm, mul_comm] using h

end PrimeFactorUnimodality
