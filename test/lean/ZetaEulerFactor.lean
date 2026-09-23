import PrimeFactorUnimodality.Helpers.Analytic.ZetaEulerFactor

/-! # Short Euler-correction interfaces and exact regression cases -/

set_option autoImplicit false

namespace PrimeFactorUnimodality.Tests

noncomputable section

open Complex Finset Polynomial
open PrimeFactorUnimodality

example (N m : ℕ) (hN : 0 < N) (s : ℂ) :
    zetaEulerCorrection N s m = (1 / (N : ℂ) ^ s) *
      ((N : ℂ) / (s - 1) - 1 / 2 +
        ∑ j ∈ range m, (bernoulliNormalizedReal (j + 2) 0 : ℂ) *
          zetaRisingFactor s (j + 1) / (N : ℂ) ^ (j + 1)) := by
  exact PrimeFactorUnimodality.zetaEulerCorrection_eq_factored N m hN s

example (N k : ℕ) (s : ℂ) :
    zetaRisingFactor s (k + 1) / (N : ℂ) ^ (k + 1) =
      (zetaRisingFactor s k / (N : ℂ) ^ k) * (s + (k : ℂ)) / N := by
  exact PrimeFactorUnimodality.zetaRisingFactor_div_pow_succ N k s

example (N m : ℕ) (hN : 0 < N) (s : ℂ) :
    zetaEulerCorrection N s m = (1 / (N : ℂ) ^ s) *
      ((N : ℂ) / (s - 1) - 1 / 2 +
        ((List.range' 1 m).map (fun j =>
          (bernoulliNormalizedReal (j + 1) 0 : ℂ) *
            (zetaRisingFactor s j / (N : ℂ) ^ j))).sum) := by
  exact PrimeFactorUnimodality.zetaEulerCorrection_eq_list N m hN s



end

end PrimeFactorUnimodality.Tests
