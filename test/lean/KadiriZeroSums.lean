import Mathlib.Logic.Equiv.Bool
import PrimeFactorUnimodality.Helpers.Analytic.KadiriOuterMaster

/-! # Multiplicity-preserving zero-pair regressions

Test full analytic order (including infinite order), fixed critical-line
labels, and signed summands whose pairs alone are nonnegative. The actual
paper-weight tests retain the outer strip rather than assuming it empty.
-/

namespace PrimeFactorUnimodality.Tests

noncomputable section

open Complex Real
open scoped ComplexConjugate

example {f : ℂ → ℂ} {z : ℂ} (hf : AnalyticAt ℂ f (conj z))
    (hz : analyticOrderAt f (conj z) = ⊤) :
    analyticOrderAt (fun w => conj (f (conj w))) z = ⊤ :=
  (analyticOrderAt_conj_conj hf).trans hz

example {f : ℂ → ℂ} {z : ℂ} (hf : AnalyticAt ℂ f (conj z)) :
    analyticOrderNatAt (fun w => conj (f (conj w))) z = analyticOrderNatAt f (conj z) :=
  analyticOrderNatAt_conj_conj hf

example (p : RiemannXiDivisorZeroIndex) :
    (riemannXiDivisorSameHeightReflection p).1.2.val = p.1.2.val ∧
      (riemannXiDivisorZeroValue (riemannXiDivisorSameHeightReflection p)).im =
        (riemannXiDivisorZeroValue p).im := by
  simp

example (p : RiemannXiDivisorZeroIndex) (hp : (riemannXiDivisorZeroValue p).re = 1 / 2) :
    riemannXiDivisorSameHeightReflection p = p :=
  (riemannXiDivisorSameHeightReflection_fixed_iff p).mpr hp

example (p : RiemannXiDivisorZeroIndex) :
    riemannXiDivisorSameHeightReflection (riemannXiDivisorSameHeightReflection p) = p :=
  riemannXiDivisorSameHeightReflection_involutive p

-- The negative summand must not be excluded by the paired-series API.
example : (if false then (2 : ℝ) else -1) + (if true then (2 : ℝ) else -1) ≤
    ∑' b : Bool, if b then (2 : ℝ) else -1 := by
  exact (Summable.of_finite (f := fun b : Bool => if b then (2 : ℝ) else -1)).pair_le_tsum_of_involution
    Equiv.boolNot Bool.involutive_not (by intro b; cases b <;> norm_num [Equiv.boolNot])
    false (by decide)

example {G : ℂ → ℝ}
    (hG : Summable (fun p : RiemannXiDivisorZeroIndex => G (riemannXiDivisorZeroValue p))) :
    (∑' p : RiemannXiDivisorZeroIndex, G (riemannXiDivisorZeroValue p)) =
      (1 / 2 : ℝ) * ∑' p : RiemannXiDivisorZeroIndex,
        (G (riemannXiDivisorZeroValue p) + G (1 - conj (riemannXiDivisorZeroValue p))) :=
  tsum_xi_divisor_eq_half_pair hG

variable {θ η η₀ σ₀ σ δ κ : ℝ}
  (hθ : π / 2 < θ ∧ θ < π) (hη : 0 < η) (hη₀ : η ≤ η₀)
  (hσ₀ : 1 / 2 < σ₀) (hσ : σ₀ ≤ σ) (hσ₁ : σ ≤ 1) (hδ : 0 < δ) (hκ : 0 ≤ κ)
  (hκ₂ : κ ≤ kadiriKappa₂ θ η₀ (2 * σ₀ - 1) δ)
  (hκ₃ : κ ≤ kadiriKappa₃ θ η₀ (2 * σ₀ - 1) δ)

example (s : ℂ) :
    Summable (fun p : RiemannXiDivisorZeroIndex =>
      smoothedLaplaceDifference (kadiriWeight θ η) (kadiriWeightSupport θ η) κ δ
        (s - riemannXiDivisorZeroValue p)) :=
  summable_kadiriWeight_zero_difference hθ hη κ δ s

example (t : ℝ) :
    0 ≤ ∑' p : {p : RiemannXiDivisorZeroIndex //
        kadiriCentralStrip σ (riemannXiDivisorZeroValue p)},
      smoothedLaplaceDifference (kadiriWeight θ η) (kadiriWeightSupport θ η) κ δ
        (((σ : ℂ) + (t : ℂ) * I) - riemannXiDivisorZeroValue p.1) :=
  kadiriWeight_central_zero_sum_nonneg hθ hη hη₀ hσ₀ hσ hσ₁ hδ hκ hκ₂ hκ₃ t

example (p : RiemannXiDivisorZeroIndex) (hp : kadiriCentralStrip σ (riemannXiDivisorZeroValue p))
    (hne : (riemannXiDivisorZeroValue p).re ≠ 1 / 2) (t : ℝ) :
    smoothedLaplaceDifference (kadiriWeight θ η) (kadiriWeightSupport θ η) κ δ
        (((σ : ℂ) + (t : ℂ) * I) - riemannXiDivisorZeroValue p) +
      smoothedLaplaceDifference (kadiriWeight θ η) (kadiriWeightSupport θ η) κ δ
        (((σ : ℂ) + (t : ℂ) * I) - (1 - conj (riemannXiDivisorZeroValue p))) +
      (∑' q : {q : RiemannXiDivisorZeroIndex //
          ¬ kadiriCentralStrip σ (riemannXiDivisorZeroValue q)},
        smoothedLaplaceDifference (kadiriWeight θ η) (kadiriWeightSupport θ η) κ δ
          (((σ : ℂ) + (t : ℂ) * I) - riemannXiDivisorZeroValue q.1)) ≤
      ∑' q : RiemannXiDivisorZeroIndex,
        smoothedLaplaceDifference (kadiriWeight θ η) (kadiriWeightSupport θ η) κ δ
          (((σ : ℂ) + (t : ℂ) * I) - riemannXiDivisorZeroValue q) :=
  kadiriWeight_retained_pair_add_outer_le hθ hη hη₀ hσ₀ hσ hσ₁ hδ hκ hκ₂ hκ₃ p hp hne t

end

end PrimeFactorUnimodality.Tests
