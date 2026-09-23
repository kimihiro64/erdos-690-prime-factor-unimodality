import Mathlib.NumberTheory.Chebyshev

/-! # The log-square theta estimate used by the direct Dusart adapters

The published short-interval width and two-term prime-counting models
need only a log-square theta error, not a fourth-power error. Keep its
coefficient and starting point explicit, including the starting endpoint.
-/

namespace PrimeFactorUnimodality

/-- An absolute theta error with two logarithmic powers on an entire ray. -/
def HasThetaLogSquaredError (C X : ℝ) : Prop :=
  ∀ x : ℝ, X ≤ x → |Chebyshev.theta x - x| ≤ C * x / Real.log x ^ 2

/-- Restricting the ray does not change the error coefficient. -/
theorem HasThetaLogSquaredError.mono {C X Y : ℝ}
    (error : HasThetaLogSquaredError C X) (hXY : X ≤ Y) :
    HasThetaLogSquaredError C Y := fun x hx => error x (hXY.trans hx)

end PrimeFactorUnimodality
