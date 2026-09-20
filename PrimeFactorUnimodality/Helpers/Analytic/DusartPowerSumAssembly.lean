import PrimeFactorUnimodality.Helpers.Analytic.DusartProof

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

namespace PrimeFactorUnimodality

noncomputable section

/- Assemble the exponent ranges used in the intermediate part of Lemma 3.3.
   The caller supplies the individual power comparisons; this theorem handles
   the ordered finite partition and its cardinality once and for all. -/
theorem dusart_power_sum_of_finite_and_tail
    {x : Real} (hx : 1 ≤ x) {N K : Nat} (q : Nat → Real)
    (hK : 4 ≤ K) (hKN : K ≤ N)
    (hfinite : ∀ k ∈ Finset.Icc 4 K,
      x ^ (1 / (k : Real)) ≤
        q k * x ^ (1 / (3 : Real)))
    (htail : ∀ k ∈ Finset.Icc (K + 1) N,
      x ^ (1 / (k : Real)) ≤
        q (K + 1) * x ^ (1 / (3 : Real))) :
    ∑ k ∈ Finset.Icc 3 N, x ^ (1 / (k : Real)) ≤
      (1 + (∑ k ∈ Finset.Icc 4 K, q k) +
        ((N - K : Nat) : Real) * q (K + 1)) *
        x ^ (1 / (3 : Real)) := by
  have hpartition : Finset.Icc 3 N =
      ({3} ∪ Finset.Icc 4 K) ∪ Finset.Icc (K + 1) N := by
    ext k
    simp only [Finset.mem_Icc, Finset.mem_union, Finset.mem_singleton]
    omega
  have hdisj₁ : Disjoint ({3} : Finset Nat) (Finset.Icc 4 K) := by
    apply Finset.disjoint_left.mpr
    intro k hk₁ hk₂
    simp only [Finset.mem_singleton] at hk₁
    simp only [Finset.mem_Icc] at hk₂
    omega
  have hdisj₂ : Disjoint (({3} : Finset Nat) ∪ Finset.Icc 4 K)
      (Finset.Icc (K + 1) N) := by
    apply Finset.disjoint_left.mpr
    intro k hk₁ hk₂
    simp only [Finset.mem_union, Finset.mem_singleton, Finset.mem_Icc] at hk₁ hk₂
    rcases hk₁ with hk₁ | hk₁ <;> omega
  rw [hpartition, Finset.sum_union hdisj₂,
    Finset.sum_union hdisj₁]
  have hfinite_sum :
      (∑ k ∈ Finset.Icc 4 K, x ^ (1 / (k : Real))) ≤
        ∑ k ∈ Finset.Icc 4 K,
          q k * x ^ (1 / (3 : Real)) := by
    apply Finset.sum_le_sum
    intro k hk
    exact hfinite k hk
  have htail_sum :
      (∑ k ∈ Finset.Icc (K + 1) N, x ^ (1 / (k : Real))) ≤
        (Finset.Icc (K + 1) N).card •
          (q (K + 1) * x ^ (1 / (3 : Real))) := by
    apply Finset.sum_le_card_nsmul
    intro k hk
    exact htail k hk
  rw [Finset.sum_singleton]
    calc
    x ^ (1 / (3 : Real)) +
          ∑ x_1 ∈ Finset.Icc 4 K, x ^ (1 / (x_1 : Real)) +
          ∑ x_1 ∈ Finset.Icc (K + 1) N, x ^ (1 / (x_1 : Real)) ≤
        x ^ (1 / (3 : Real)) +
          ∑ k ∈ Finset.Icc 4 K,
            q k * x ^ (1 / (3 : Real)) +
          (Finset.Icc (K + 1) N).card •
            (q (K + 1) * x ^ (1 / (3 : Real))) := by
      exact add_le_add (add_le_add le_rfl hfinite_sum) htail_sum
    _ = (1 + (∑ k ∈ Finset.Icc 4 K, q k) +
        ((N - K : Nat) : Real) * q (K + 1)) *
        x ^ (1 / (3 : Real)) := by
      rw [nsmul_eq_mul, Nat.card_Icc]
      have hsub : K + 1 ≤ N + 1 := by omega
      rw [Nat.cast_sub hsub]
      push_cast
      rw [Finset.mul_sum]
      ring

end

end PrimeFactorUnimodality
