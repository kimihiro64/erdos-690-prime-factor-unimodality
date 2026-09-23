import PrimeFactorUnimodality.Helpers.Analytic.XiZeroExhaustion

/-! # Exact statement regressions for critical-line verification -/

namespace PrimeFactorUnimodality.Tests

open Complex Finset Set XiSignRows

example {T : ℝ} {n : ℕ}
    (f : Fin n → RiemannXiDivisorZeroIndex) (hf : Function.Injective f)
    (hmem : ∀ i, f i ∈ xiStrictPositiveHeightIndices T)
    (hline : ∀ i, (riemannXiDivisorZeroValue (f i)).re = 1 / 2)
    (hcount : xiStrictZeroCount T ≤ n) :
    ∀ p ∈ xiStrictPositiveHeightIndices T, (riemannXiDivisorZeroValue p).re = 1 / 2 := by
  exact xiStrict_criticalLine_of_index_family f hf hmem hline hcount

example {T : ℝ}
    (hline : ∀ p ∈ xiStrictPositiveHeightIndices T, (riemannXiDivisorZeroValue p).re = 1 / 2) :
    ∀ p ∈ xiLowHeightIndices T, (riemannXiDivisorZeroValue p).re = 1 / 2 := by
  exact xiLow_criticalLine_of_positive hline

example {n : ℕ} {rows : Fin n → XiSignRow} {a b : ℚ} {T : ℝ}
    (h : Valid rows a b) (ha : 0 ≤ a) (hb : (b : ℝ) ≤ T) :
    ∃ f : Fin n → RiemannXiDivisorZeroIndex, Function.Injective f ∧
      (∀ i, f i ∈ xiStrictPositiveHeightIndices T) ∧
      ∀ i, (riemannXiDivisorZeroValue (f i)).re = 1 / 2 := by
  exact h.exists_strict_indices ha hb

example {n : ℕ} {rows : Fin n → XiSignRow} {a b : ℚ} {T : ℝ}
    (h : Valid rows a b) (ha : 0 ≤ a) (hb : (b : ℝ) ≤ T) : n ≤ xiStrictZeroCount T := by
  exact h.le_strict_count ha hb

example {n : ℕ} {rows : Fin n → XiSignRow} {a b : ℚ} {T : ℝ}
    (h : Valid rows a b) (ha : 0 ≤ a) (hb : (b : ℝ) ≤ T) (hcount : xiStrictZeroCount T ≤ n) :
    ∀ p ∈ xiLowHeightIndices T, (riemannXiDivisorZeroValue p).re = 1 / 2 := by
  exact h.low_criticalLine ha hb hcount

example : xiStrictZeroCount 0 = 0 := by
  have he : xiStrictPositiveHeightIndices 0 = ∅ := by
    ext p
    simp only [mem_xiStrictPositiveHeightIndices, Finset.notMem_empty, iff_false]
    exact fun h => lt_asymm h.1 h.2
  simp only [xiStrictZeroCount, he, Finset.card_empty]

example {n : ℕ} {rows : Fin n → XiSignRow} {a b : ℚ}
    (h : Valid rows a b) (ha : 0 ≤ a) (hcount : xiStrictZeroCount (b : ℝ) ≤ n) :
    ∀ p ∈ xiLowHeightIndices (b : ℝ), (riemannXiDivisorZeroValue p).re = 1 / 2 :=
  h.low_criticalLine ha le_rfl hcount

example {T : ℝ}
    (hline : ∀ p ∈ xiStrictPositiveHeightIndices T, (riemannXiDivisorZeroValue p).re = 1 / 2)
    (p : RiemannXiDivisorZeroIndex) (hp : (riemannXiDivisorZeroValue p).im < 0)
    (hT : -(riemannXiDivisorZeroValue p).im < T) : (riemannXiDivisorZeroValue p).re = 1 / 2 := by
  apply xiLow_criticalLine_of_positive hline p
  rw [mem_xiLowHeightIndices, abs_of_neg hp]
  exact hT

end PrimeFactorUnimodality.Tests
