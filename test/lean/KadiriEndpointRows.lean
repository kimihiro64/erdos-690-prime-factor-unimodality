import PrimeFactorUnimodality.Helpers.Analytic.KadiriEndpointRows

/-! # Exact statement regressions for the endpoint bootstrap increment -/

namespace PrimeFactorUnimodality.Tests

open Finset Real

example {row : KadiriEndpointRow} {R r T : ℝ} {n : ℕ} {a : ℕ → ℝ}
    (h : row.Valid R r T n a)
    (ha : ∀ i ∈ Finset.range (n + 1), 0 ≤ a i) (ha₀ : 0 < a 0) (ha₁ : 0 < a 1)
    (hpoly : ∀ u : ℝ, 0 ≤ ∑ i ∈ Finset.range (n + 1), a i * cos ((i : ℝ) * u))
    (hlow : ∀ p : RiemannXiDivisorZeroIndex,
      |(riemannXiDivisorZeroValue p).im| < T → (riemannXiDivisorZeroValue p).re ≤ 1 / 2)
    (hhigh : KadiriHighRegion R T) : KadiriHighRegion r T := by
  apply PrimeFactorUnimodality.KadiriEndpointRow.Valid.highRegion <;> assumption

example {row : KadiriEndpointRow} {R r T : ℝ}
    {n : ℕ} {a : ℕ → ℝ} (h : row.Valid R r T n a) : KadiriEndpointChain n a T R r := by
  apply PrimeFactorUnimodality.KadiriEndpointRow.Valid.chain <;> assumption

example {n : ℕ} {a : ℕ → ℝ} {T R r s : ℝ}
    (h : KadiriEndpointChain n a T R r) (h' : KadiriEndpointChain n a T r s) :
    KadiriEndpointChain n a T R s := by
  apply PrimeFactorUnimodality.KadiriEndpointChain.append <;> assumption

example {n : ℕ} {a : ℕ → ℝ} {T R r : ℝ}
    (h : KadiriEndpointChain n a T R r)
    (ha : ∀ i ∈ Finset.range (n + 1), 0 ≤ a i) (ha₀ : 0 < a 0) (ha₁ : 0 < a 1)
    (hpoly : ∀ u : ℝ, 0 ≤ ∑ i ∈ Finset.range (n + 1), a i * cos ((i : ℝ) * u))
    (hlow : ∀ p : RiemannXiDivisorZeroIndex,
      |(riemannXiDivisorZeroValue p).im| < T → (riemannXiDivisorZeroValue p).re ≤ 1 / 2)
    (hhigh : KadiriHighRegion R T) : KadiriHighRegion r T := by
  apply PrimeFactorUnimodality.KadiriEndpointChain.highRegion <;> assumption

example (n : ℕ) (a : ℕ → ℝ) (T R : ℝ) : KadiriEndpointChain n a T R R :=
  Relation.ReflTransGen.refl

end PrimeFactorUnimodality.Tests
