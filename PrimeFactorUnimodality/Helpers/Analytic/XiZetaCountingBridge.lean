import PrimeFactorUnimodality.Helpers.Analytic.XiZeroCountingEndpoints
import PrimeFactorUnimodality.Helpers.Analytic.ZetaXiMultiplicity

/-! # Exact bridge from the xi divisor count to the PNT zeta count

The pinned PNT `riemannZeta.N` sums integer orders over `0<Im(z)<T`.
Finite xi fibers have exactly those orders. Grouping the actual divisor
labels by complex value identifies the strict count with `N`, not the
closed count. The latter is its right-hand limit and retains every cutoff
multiplicity. Quantitative estimates below still require their stated
counting hypothesis.
-/

namespace PrimeFactorUnimodality

noncomputable section

open Complex Filter Real Set
open scoped Topology

private def xiStrictZeroValues (T : ℝ) : Finset ℂ :=
  (xiStrictPositiveHeightIndices T).image riemannXiDivisorZeroValue

private theorem mem_xiStrictZeroValues (T : ℝ) (z : ℂ) :
    z ∈ xiStrictZeroValues T ↔ z ∈ riemannZeta.zeroes_rect univ (Ioo 0 T) := by
  classical
  constructor
  · intro hz
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hz
    have hp' := (mem_xiStrictPositiveHeightIndices T p).mp hp
    have hxi := riemannXiDivisorZeroValue_eq_zero p
    have hre := (riemannXi_zero_mem_open_critical_strip hxi).1
    have h1 : riemannXiDivisorZeroValue p ≠ 1 := by
      intro h
      simpa [h] using hp'.1
    exact ⟨mem_univ _, hp', (riemannXi_eq_zero_iff_riemannZeta_eq_zero hre h1).mp hxi⟩
  · intro hz
    have him : 0 < z.im ∧ z.im < T := hz.2.1
    obtain ⟨p, hp⟩ := exists_xi_divisor_index_of_zero
      (riemannXi_eq_zero_of_zeta_zero_of_im_ne_zero him.1.ne' hz.2.2)
    apply Finset.mem_image.mpr
    exact ⟨p, (mem_xiStrictPositiveHeightIndices T p).mpr (by simpa only [hp] using him), hp⟩

/-- Finiteness of the PNT positive rectangle follows from the actual xi labels. -/
theorem finite_zeta_positive_height_via_xi (T : ℝ) :
    (riemannZeta.zeroes_rect univ (Ioo 0 T)).Finite := by
  have heq : (xiStrictZeroValues T : Set ℂ) = riemannZeta.zeroes_rect univ (Ioo 0 T) :=
    Set.ext (mem_xiStrictZeroValues T)
  rw [← heq]
  exact (xiStrictZeroValues T).finite_toSet

/-- PNT's strict count counts exactly the xi divisor labels, with multiplicity. -/
theorem xiStrictZeroCount_eq_zeta_N (T : ℝ) :
    (xiStrictZeroCount T : ℝ) = riemannZeta.N T := by
  classical
  let : Fintype (riemannZeta.zeroes_rect univ (Ioo 0 T)) :=
    (finite_zeta_positive_height_via_xi T).fintype
  have hf (z : ℂ) (hz : z ∈ xiStrictZeroValues T) :
      ((xiStrictPositiveHeightIndices T).filter
        (fun p => riemannXiDivisorZeroValue p = z)).card = analyticOrderNatAt riemannXi z := by
    have hz' := (mem_xiStrictZeroValues T z).mp hz
    have h0 : z ≠ 0 := by intro h; simpa [h] using hz'.2.1.1
    have heq : (xiStrictPositiveHeightIndices T).filter
        (fun p => riemannXiDivisorZeroValue p = z) =
          Hadamard.divisorZeroIndex₀_fiberFinset riemannXi z := by
      ext p
      simp only [Finset.mem_filter, mem_xiStrictPositiveHeightIndices,
        Hadamard.mem_divisorZeroIndex₀_fiberFinset]
      exact ⟨fun h => h.2, fun h => ⟨by simpa only [h, mem_Ioo] using hz'.2.1, h⟩⟩
    rw [heq]
    exact Hadamard.divisorZeroIndex₀_fiberFinset_card_eq_analyticOrderNatAt
      differentiable_riemannXi h0
  calc
    _ = ∑ z ∈ xiStrictZeroValues T,
        (((xiStrictPositiveHeightIndices T).filter
          (fun p => riemannXiDivisorZeroValue p = z)).card : ℝ) := by
      exact_mod_cast Finset.card_eq_sum_card_image
        riemannXiDivisorZeroValue (xiStrictPositiveHeightIndices T)
    _ = ∑ z ∈ xiStrictZeroValues T, (riemannZeta.order z : ℝ) := by
      apply Finset.sum_congr rfl
      intro z hz
      rw [hf z hz]
      have hz' := (mem_xiStrictZeroValues T z).mp hz
      have hxi := riemannXi_eq_zero_of_zeta_zero_of_im_ne_zero hz'.2.1.1.ne' hz'.2.2
      have h1 : z ≠ 1 := by intro h; simpa [h] using hz'.2.1.1
      have horder := xi_divisor_eq_zeta_order (riemannXi_zero_mem_open_critical_strip hxi).1 h1
      rw [Hadamard.divisor_univ_eq_analyticOrderNatAt_int differentiable_riemannXi] at horder
      exact_mod_cast horder
    _ = ∑' z : riemannZeta.zeroes_rect univ (Ioo 0 T), (riemannZeta.order z : ℝ) := by
      rw [tsum_fintype]
      exact Finset.sum_subtype (xiStrictZeroValues T) (mem_xiStrictZeroValues T)
        (fun z => (riemannZeta.order z : ℝ))
    _ = riemannZeta.N T := by simp only [riemannZeta.N, riemannZeta.zeroes_sum, one_mul]

/-- The closed count is the strict PNT count plus the entire cutoff multiplicity. -/
theorem xiZeroCount_eq_zeta_N_add_multiplicity {T : ℝ} (hT : 0 < T) :
    (xiZeroCount T : ℝ) = riemannZeta.N T + (xiOrdinateMultiplicity T : ℝ) := by
  rw [xiZeroCount_eq_strict_add_multiplicity hT, Nat.cast_add, xiStrictZeroCount_eq_zeta_N]

/-- PNT's strict counting function tends to the closed xi count from the right. -/
theorem tendsto_zeta_N_right (T : ℝ) :
    Tendsto riemannZeta.N (𝓝[>] T) (𝓝 (xiZeroCount T : ℝ)) := by
  simpa only [xiStrictZeroCount_eq_zeta_N] using tendsto_xiStrictZeroCount_right T

/-- A proved zeta counting bound supplies the actual closed-count Lehman premise. -/
theorem xiZeroCountingRemainder_le_of_zeta_count {A : ℝ} (hA : 0 < A)
    (h : ∀ x, A < x → |riemannZeta.N x - xiZeroCountingMainTerm x| ≤ 2 * Real.log x) :
    ∀ x ∈ Ici A, |xiZeroCountingRemainder x| ≤ 2 * Real.log x := by
  apply xiZeroCountingRemainder_le_of_strict hA
  simpa only [xiStrictZeroCount_eq_zeta_N] using h

end

end PrimeFactorUnimodality
