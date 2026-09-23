import PrimeFactorUnimodality.Helpers.Analytic.DusartBoxRosserMixed

/-! # Regression tests for complete Rosser cutoff selection -/

namespace PrimeFactorUnimodality.Tests

open Chebyshev Real

example (m : ℕ) {x R ν H : ℝ}
    (hx : 1 < x) (hR : 0 < R) (hν : 0 < ν) (hH : 20 ≤ H)
    (hmargin : 1 < (m + 3 : ℕ) * ν ^ 2) :
    exp (sqrt ((Real.log x / R) / (m + 4 : ℕ))) ≤ H ∨
      dusartRosserGrowthDomain m x R ν H :=
  dusartRosserGrowthDomain_or_fixed m hx hR hν hH hmargin

example (m : ℕ) (s x R ν a H δ : ℝ)
    (hg : dusartRosserGrowthDomain m x R ν H) :
    dusartBoxRosserMixedBudget m s x R ν a H δ =
      dusartBoxRosserRelativeBudget m s x R ν a H δ :=
  dusartBoxRosserMixedBudget_of_growth m s x R ν a H δ hg

example (m : ℕ) (s x R ν a H δ : ℝ)
    (hg : ¬ dusartRosserGrowthDomain m x R ν H) :
    dusartBoxRosserMixedBudget m s x R ν a H δ =
      dusartBoxRosserFixedRelativeBudget m s x R (m + 3 : ℕ) a H δ :=
  dusartBoxRosserMixedBudget_of_fixed m s x R ν a H δ hg

example (m : ℕ) {s x R ν a H δ : ℝ}
    (hs : 0 < s) (hx : 1 < x) (hR : 0 < R) (hν : 0 < ν) (hν1 : ν ≤ 1)
    (hmargin : 1 < (m + 3 : ℕ) * ν ^ 2)
    (ha : 10 ≤ a) (haH : a < H) (hH : 10 ^ 9 ≤ H) (hδ : 0 < δ)
    (hgap : ∀ z ∈ xiLowHeightIndices H, (riemannXiDivisorZeroValue z).re ≤ 1 - δ)
    (hreg : ∀ z : RiemannXiDivisorZeroIndex, H ≤ |(riemannXiDivisorZeroValue z).im| →
      (riemannXiDivisorZeroValue z).re ≤
        1 - 1 / (R * Real.log |(riemannXiDivisorZeroValue z).im|)) :
    |dusartPsiAverageError (m + 3) (s * x) x| / x ≤
      dusartBoxRosserMixedBudget m s x R ν a H δ :=
  abs_dusartPsiAverageError_div_le_rosserMixed m hs hx hR hν hν1 hmargin ha haH hH hδ hgap hreg

example (m : ℕ) {s x R ν a H δ : ℝ}
    (hs : 0 < s) (hx : 0 < x) (hl : 1 < x * (1 - (m + 3 : ℕ) * s))
    (hR : 0 < R) (hν : 0 < ν) (hν1 : ν ≤ 1) (hmargin : 1 < (m + 3 : ℕ) * ν ^ 2)
    (ha : 10 ≤ a) (haH : a < H) (hH : 10 ^ 9 ≤ H) (hδ : 0 < δ)
    (hgap : ∀ z ∈ xiLowHeightIndices H, (riemannXiDivisorZeroValue z).re ≤ 1 - δ)
    (hreg : ∀ z : RiemannXiDivisorZeroIndex, H ≤ |(riemannXiDivisorZeroValue z).im| →
      (riemannXiDivisorZeroValue z).re ≤
        1 - 1 / (R * Real.log |(riemannXiDivisorZeroValue z).im|)) :
    |ψ x - x| / x ≤
      max ((1 - (m + 3 : ℕ) * s) *
        dusartBoxRosserMixedBudget m (s / (1 - (m + 3 : ℕ) * s))
          (x * (1 - (m + 3 : ℕ) * s)) R ν a H δ)
        (dusartBoxRosserMixedBudget m s x R ν a H δ) + (m + 3 : ℕ) * s / 2 :=
  abs_psi_sub_div_le_dusartBoxRosserMixed m hs hx hl hR hν hν1 hmargin ha haH hH hδ hgap hreg

-- Equality of the fixed and growing cutoff belongs to the growing domain.
example (m : ℕ) (s x R ν a δ : ℝ)
    (hp : Real.log (2 * π) ≤ 1 / (m + 3 : ℕ) + sqrt ((Real.log x / R) / (m + 3 : ℕ))) :
    dusartBoxRosserMixedBudget m s x R ν a (exp (ν * sqrt (Real.log x / R))) δ =
      dusartBoxRosserRelativeBudget m s x R ν a (exp (ν * sqrt (Real.log x / R))) δ :=
  dusartBoxRosserMixedBudget_of_growth _ _ _ _ _ _ _ _ ⟨le_rfl, hp⟩

example (m : ℕ) (s x R ν a H δ : ℝ) (hc : exp (ν * sqrt (Real.log x / R)) < H) :
    dusartBoxRosserMixedBudget m s x R ν a H δ =
      dusartBoxRosserFixedRelativeBudget m s x R (m + 3 : ℕ) a H δ :=
  dusartBoxRosserMixedBudget_of_fixed _ _ _ _ _ _ _ _ (fun hg => (not_le.mpr hc) hg.1)

example (m : ℕ) (s x R ν a H δ : ℝ)
    (hp : 1 / (m + 3 : ℕ) + sqrt ((Real.log x / R) / (m + 3 : ℕ)) < Real.log (2 * π)) :
    dusartBoxRosserMixedBudget m s x R ν a H δ =
      dusartBoxRosserFixedRelativeBudget m s x R (m + 3 : ℕ) a H δ :=
  dusartBoxRosserMixedBudget_of_fixed _ _ _ _ _ _ _ _ (fun hg => (not_le.mpr hp) hg.2)

-- The actual pointwise estimate permits distinct branches on the two sides.
example (m : ℕ) {s x R ν a H δ : ℝ}
    (hs : 0 < s) (hx : 0 < x) (hl : 1 < x * (1 - (m + 3 : ℕ) * s))
    (hR : 0 < R) (hν : 0 < ν) (hν1 : ν ≤ 1) (hmargin : 1 < (m + 3 : ℕ) * ν ^ 2)
    (ha : 10 ≤ a) (haH : a < H) (hH : 10 ^ 9 ≤ H) (hδ : 0 < δ)
    (hgap : ∀ z ∈ xiLowHeightIndices H, (riemannXiDivisorZeroValue z).re ≤ 1 - δ)
    (hreg : ∀ z : RiemannXiDivisorZeroIndex, H ≤ |(riemannXiDivisorZeroValue z).im| →
      (riemannXiDivisorZeroValue z).re ≤
        1 - 1 / (R * Real.log |(riemannXiDivisorZeroValue z).im|))
    (hleft : ¬ dusartRosserGrowthDomain m (x * (1 - (m + 3 : ℕ) * s)) R ν H)
    (hright : dusartRosserGrowthDomain m x R ν H) :
    |ψ x - x| / x ≤
      max ((1 - (m + 3 : ℕ) * s) *
        dusartBoxRosserFixedRelativeBudget m (s / (1 - (m + 3 : ℕ) * s))
          (x * (1 - (m + 3 : ℕ) * s)) R (m + 3 : ℕ) a H δ)
        (dusartBoxRosserRelativeBudget m s x R ν a H δ) + (m + 3 : ℕ) * s / 2 := by
  have h := abs_psi_sub_div_le_dusartBoxRosserMixed m hs hx hl hR hν hν1 hmargin ha haH hH hδ hgap hreg
  rw [dusartBoxRosserMixedBudget_of_fixed _ _ _ _ _ _ _ _ hleft,
    dusartBoxRosserMixedBudget_of_growth _ _ _ _ _ _ _ _ hright] at h
  exact h

end PrimeFactorUnimodality.Tests
