import PrimeFactorUnimodality.Helpers.Analytic.DusartBillionCutoffTheta

/-! # Three-billion analytic bridge and all interval seams -/

set_option autoImplicit false

namespace PrimeFactorUnimodality.Tests

open Real Chebyshev

example {x₀ x r B : ℝ} (hx₀ : (3000000000 : ℝ) ≤ x₀) (hr : 2 ≤ r)
    (hrx : r ^ 2 ≤ x₀ * (1 - 3 * (1 / 50000))) (hx : x₀ ≤ x) (hB : log x ≤ B)
    (hcap : (dusartEarlierAverageCap r + 3 / 100000 + (8 / 5) / r) * B ^ 2 ≤ (1 / 5 : ℝ))
    (hgap : ∀ z ∈ xiLowHeightIndices 25000000,
      (riemannXiDivisorZeroValue z).re ≤ (1 / 2 : ℝ)) :
    |θ x - x| ≤ (1 / 5 : ℝ) * x / log x ^ 2 :=
  abs_theta_sub_le_logSquared_of_sharper_cap hx₀ hr hrx hx hB hcap hgap

example (hgap : ∀ z ∈ xiLowHeightIndices 25000000,
    (riemannXiDivisorZeroValue z).re ≤ (1 / 2 : ℝ)) :
    ∀ x ∈ ({3000000000, 3400000000, 5000000000, 10000000000, 1441000000000} : Finset ℝ),
      |θ x - x| ≤ (1 / 5 : ℝ) * x / log x ^ 2 := by
  intro x hx
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl <;>
    exact abs_theta_sub_le_logSquared_billion_bridge (by norm_num) (by norm_num) hgap

example (hgap : ∀ z ∈ xiLowHeightIndices 25000000,
    (riemannXiDivisorZeroValue z).re ≤ (1 / 2 : ℝ)) :
    |θ 3400000000 - 3400000000| ≤ (1 / 5 : ℝ) * 3400000000 / log 3400000000 ^ 2 := by
  have first := abs_theta_sub_le_logSquared_billion_first
    (x := 3400000000) (by norm_num) (by norm_num) hgap
  have second := abs_theta_sub_le_logSquared_billion_second
    (x := 3400000000) (by norm_num) (by norm_num) hgap
  exact first.trans_eq (by rfl)

example (hgap : ∀ z ∈ xiLowHeightIndices 25000000,
    (riemannXiDivisorZeroValue z).re ≤ (1 / 2 : ℝ)) :
    |θ 5000000000 - 5000000000| ≤ (1 / 5 : ℝ) * 5000000000 / log 5000000000 ^ 2 := by
  have second := abs_theta_sub_le_logSquared_billion_second
    (x := 5000000000) (by norm_num) (by norm_num) hgap
  have third := abs_theta_sub_le_logSquared_billion_third
    (x := 5000000000) (by norm_num) (by norm_num) hgap
  exact second.trans_eq (by rfl)

end PrimeFactorUnimodality.Tests
