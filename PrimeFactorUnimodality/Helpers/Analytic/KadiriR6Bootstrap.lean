import PrimeFactorUnimodality.Helpers.Analytic.KadiriR6Parameters
import PrimeFactorUnimodality.Helpers.Analytic.ZetaZeroFreeInitial

/-! # The actual region at six from a checked endpoint chain

Start from the proved unconditional region at 56, reuse the exact polynomial
and its checked coefficient signs, and keep the low critical-line input
explicit. The finite chain's validity is still required: this module does
not assert any unchecked correction or transform margin.
-/

namespace PrimeFactorUnimodality

noncomputable section

open Real

/-- A checked chain uses the initial actual region, not an assumed region at its starting point. -/
theorem xi_zero_gap_six_of_endpoint_chain
    (hchain : KadiriEndpointChain 16 mossinghoffTrudgianCoefficient 1000000000 56 6)
    (hlow : ∀ z ∈ xiLowHeightIndices 1000000000,
      (riemannXiDivisorZeroValue z).re ≤ (1 / 2 : ℝ)) : KadiriHighRegion 6 1000000000 := by
  apply hchain.highRegion
    (fun i hi => mossinghoffTrudgianCoefficient_nonneg (Finset.mem_range.mp hi))
    (by simp) mossinghoffTrudgianCoefficient_one_pos mossinghoffTrudgianPolynomial_nonneg
    (fun p hp => hlow p ((mem_xiLowHeightIndices 1000000000 p).mpr hp))
  intro p hp
  exact xi_zero_gap_initial (riemannXiDivisorZeroValue_eq_zero p) (by norm_num at hp ⊢; exact hp)

/-- Three endpoint rows suffice; their common angle and separation data are stored only once. -/
theorem xi_zero_gap_six_of_three_endpoint_rows
    (h₁ : kadiriSixRow.Valid 56 8 1000000000 16 mossinghoffTrudgianCoefficient)
    (h₂ : kadiriSixRow.Valid 8 (13 / 2) 1000000000 16 mossinghoffTrudgianCoefficient)
    (h₃ : kadiriSixRow.Valid (13 / 2) 6 1000000000 16 mossinghoffTrudgianCoefficient)
    (hlow : ∀ z ∈ xiLowHeightIndices 1000000000,
      (riemannXiDivisorZeroValue z).re ≤ (1 / 2 : ℝ)) :
    ∀ z : RiemannXiDivisorZeroIndex, (1000000000 : ℝ) ≤
      |(riemannXiDivisorZeroValue z).im| → (riemannXiDivisorZeroValue z).re ≤
        1 - 1 / (6 * Real.log |(riemannXiDivisorZeroValue z).im|) := by
  have h := xi_zero_gap_six_of_endpoint_chain (h₁.chain.append h₂.chain |>.append h₃.chain) hlow
  intro z hz
  linarith [h z hz]

end

end PrimeFactorUnimodality
