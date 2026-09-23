import PrimeFactorUnimodality.Helpers.Analytic.KadiriInitialCutoff

/-! # Unconditional initial regions at decimal cutoffs

Every example uses the proved region, not a supplied finite RH or region premise.
-/

set_option autoImplicit false

namespace PrimeFactorUnimodality.Tests

noncomputable section

open Real

example {R T : ℝ} (hT : 1 < T) (hR : 56 ≤ R)
    (hscale : 56 * log (10 ^ 9 : ℝ) ≤ R * log T) : KadiriHighRegion R T :=
  kadiriHighRegion_of_initial_cutoff hT hR hscale

example {n : ℕ} (hn : 1 ≤ n) (hn9 : n ≤ 9) :
    KadiriHighRegion (504 / (n : ℝ)) (10 ^ n) :=
  kadiriHighRegion_decimal_cutoff hn hn9

example : KadiriHighRegion (504) 10 := by
  convert kadiriHighRegion_decimal_cutoff (n := 1) (by norm_num) (by norm_num) using 1 <;>
    norm_num

example : KadiriHighRegion (252) 100 := by
  convert kadiriHighRegion_decimal_cutoff (n := 2) (by norm_num) (by norm_num) using 1 <;>
    norm_num

example : KadiriHighRegion (168) 1000 := by
  convert kadiriHighRegion_decimal_cutoff (n := 3) (by norm_num) (by norm_num) using 1 <;>
    norm_num

example : KadiriHighRegion (84) 1000000 := by
  convert kadiriHighRegion_decimal_cutoff (n := 6) (by norm_num) (by norm_num) using 1 <;>
    norm_num

example : KadiriHighRegion (72) 10000000 := by
  convert kadiriHighRegion_decimal_cutoff (n := 7) (by norm_num) (by norm_num) using 1 <;>
    norm_num

example : KadiriHighRegion (63) 100000000 := by
  convert kadiriHighRegion_decimal_cutoff (n := 8) (by norm_num) (by norm_num) using 1 <;>
    norm_num

example : KadiriHighRegion (56) 1000000000 := by
  convert kadiriHighRegion_decimal_cutoff (n := 9) (by norm_num) (by norm_num) using 1 <;>
    norm_num

example {n : ℕ} {a : ℕ → ℝ} {T R r : ℝ}
    (h : KadiriEndpointChain n a T R r) (hT : 1 < T) (hR : 56 ≤ R)
    (hscale : 56 * log (10 ^ 9 : ℝ) ≤ R * log T)
    (ha : ∀ i ∈ Finset.range (n + 1), 0 ≤ a i) (ha₀ : 0 < a 0) (ha₁ : 0 < a 1)
    (hpoly : ∀ u : ℝ, 0 ≤ ∑ i ∈ Finset.range (n + 1), a i * cos ((i : ℝ) * u))
    (hlow : ∀ p : RiemannXiDivisorZeroIndex,
      |(riemannXiDivisorZeroValue p).im| < T → (riemannXiDivisorZeroValue p).re ≤ 1 / 2) :
    KadiriHighRegion r T :=
  h.highRegion_of_initial_cutoff hT hR hscale ha ha₀ ha₁ hpoly hlow

end

end PrimeFactorUnimodality.Tests
