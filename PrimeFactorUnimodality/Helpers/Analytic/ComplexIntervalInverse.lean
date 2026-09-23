import PrimeFactorUnimodality.Helpers.Analytic.ComplexInterval

/-! # Checked inverses of complex rectangles

Inversion returns an enclosure only when the computed squared-norm interval
is strictly positive. Failure is explicit, including rectangles containing
zero. No division by an unchecked interval endpoint is accepted.
-/

namespace PrimeFactorUnimodality.ComplexInterval

open Complex LeanCert.Core

/-- A rational enclosure of the squared complex norm. -/
def normSquared (J : ComplexInterval) : IntervalRat :=
  IntervalRat.add (IntervalRat.mul J.re J.re) (IntervalRat.mul J.im J.im)

/-- Both coordinate products contribute to the squared norm enclosure. -/
theorem mem_normSquared {z : ℂ} {J : ComplexInterval} (hz : z ∈ J) :
    Complex.normSq z ∈ normSquared J := by
  exact IntervalRat.mem_add (IntervalRat.mem_mul hz.1 hz.1) (IntervalRat.mem_mul hz.2 hz.2)

/-- Inversion is accepted only after strict separation from zero is checked. -/
def inverse? (J : ComplexInterval) : Option ComplexInterval :=
  let D := normSquared J
  if h : 0 < D.lo then
    let R := IntervalRat.invNonzero ⟨D, fun hz => (not_le_of_gt h) hz.1⟩
    some ⟨IntervalRat.mul J.re R, IntervalRat.scale (-1) (IntervalRat.mul J.im R)⟩
  else none

/-- Every accepted inverse rectangle encloses the actual reciprocal. -/
theorem mem_inverse {J K : ComplexInterval} (h : inverse? J = some K)
    {z : ℂ} (hz : z ∈ J) : z⁻¹ ∈ K := by
  unfold inverse? at h
  dsimp only at h
  split at h
  next hpos =>
    cases Option.some.inj h
    have hn := mem_normSquared hz
    have hnpos : 0 < Complex.normSq z := lt_of_lt_of_le (Rat.cast_pos.mpr hpos) hn.1
    have hi := IntervalRat.mem_invNonzero
      (I := ⟨normSquared J, fun hz => (not_le_of_gt hpos) hz.1⟩) hn hnpos.ne'
    constructor
    · simpa only [Complex.inv_re, div_eq_mul_inv] using IntervalRat.mem_mul hz.1 hi
    · simpa only [Complex.inv_im, div_eq_mul_inv, Rat.cast_neg, Rat.cast_one, neg_one_mul,
        neg_mul, one_mul] using IntervalRat.mem_scale (-1) (IntervalRat.mem_mul hz.2 hi)
  next => cases h

end PrimeFactorUnimodality.ComplexInterval
