import PrimeFactorUnimodality.Helpers.Analytic.DirichletAtomIntervals

/-! # Shared-moment interfaces and small rational regression cases -/

set_option autoImplicit false

namespace PrimeFactorUnimodality.Tests

noncomputable section

open Complex Finset LeanCert.Core
open PrimeFactorUnimodality

variable {degree : ℕ}

example {L P : IntervalRat} {x : ℝ}
    (hx : x ∈ L) (hpi : Real.pi ∈ P) (base : ℚ) (turns : ℤ) :
    -(base : ℝ) * x - (turns : ℝ) * (2 * Real.pi) ∈
      dirichletReducedPhase L P base turns := by
  exact PrimeFactorUnimodality.mem_dirichletReducedPhase hx hpi base turns

example {c : SharedTaylorIntervals} (hc : c.Prepared)
    {P : IntervalRat} (hpi : Real.pi ∈ P) (base radius : ℚ)
    (n : ℕ) (hn : 0 < n) (bin turns : ℤ) :
    1 / (n : ℂ) ^ ((1 / 2 : ℂ) + (base : ℂ) * I) ∈
        (dirichletAtomInterval c P base radius n bin turns).weight ∧
      -(radius : ℝ) * Real.log n - bin ∈
        (dirichletAtomInterval c P base radius n bin turns).residual := by
  exact PrimeFactorUnimodality.dirichletAtomInterval_sound hc hpi base radius n hn bin turns



end

end PrimeFactorUnimodality.Tests
