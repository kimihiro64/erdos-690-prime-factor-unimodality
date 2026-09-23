import PrimeFactorUnimodality.Helpers.Analytic.XiLowConjugatePartition

/-! # Signed low-zero sums retain every multiplicity and the strict cutoff -/

open PrimeFactorUnimodality Finset

example {E : Type*} [AddCommMonoid E] (T : ℝ) (w : RiemannXiDivisorZeroIndex → E) :
    (∑ p ∈ xiLowHeightIndices T, w p) =
      ∑ p ∈ xiStrictPositiveHeightIndices T, (w p + w (riemannXiDivisorConjugation p)) :=
  sum_xiLow_eq_positive_conjugate T w

example (T : ℝ) :
    Disjoint (xiStrictPositiveHeightIndices T)
      ((xiStrictPositiveHeightIndices T).map riemannXiDivisorConjugation.toEmbedding) :=
  disjoint_xiStrictPositive_conjugate T

example (T : ℝ) (p : RiemannXiDivisorZeroIndex)
    (hp : |(riemannXiDivisorZeroValue p).im| = T) : p ∉ xiLowHeightIndices T := by
  rw [mem_xiLowHeightIndices, hp]
  exact lt_irrefl T

example {E : Type*} [AddCommMonoid E] (w : RiemannXiDivisorZeroIndex → E) :
    (∑ p ∈ xiLowHeightIndices 0, w p) = 0 := by
  have he : xiLowHeightIndices 0 = ∅ := by
    ext p
    simp only [mem_xiLowHeightIndices, notMem_empty, iff_false]
    exact not_lt_of_ge (abs_nonneg _)
  rw [he, sum_empty]
