import PrimeFactorUnimodality.Helpers.Analytic.ZetaXiHadamardConstant

/-! # Exact finite subtraction from the unconditional xi reciprocal mass

The real reciprocal divisor sum is known exactly without RH. Bounded
ordinate sets are finite because xi zeros lie in the closed critical strip
and the actual divisor is locally finite. Subtracting the strict low-height
part leaves the closed tail, including every zero at the cutoff.
-/

namespace PrimeFactorUnimodality

noncomputable section

open Complex Real

/-- Bounded ordinates give a finite set of xi divisor labels, including multiplicities. -/
theorem finite_xi_divisor_abs_im_le (H : ℝ) :
    {p : RiemannXiDivisorZeroIndex | |(riemannXiDivisorZeroValue p).im| ≤ H}.Finite := by
  apply (Hadamard.divisorZeroIndex₀_norm_le_finite
    (f := riemannXi) (U := Set.univ) (B := 1 + H) (by simp)).subset
  intro p hp
  change |(riemannXiDivisorZeroValue p).im| ≤ H at hp
  obtain ⟨hβ₀, hβ₁⟩ := riemannXi_zero_mem_critical_strip (riemannXiDivisorZeroValue_eq_zero p)
  have hn := norm_le_abs_re_add_abs_im (riemannXiDivisorZeroValue p)
  rw [abs_of_nonneg hβ₀] at hn
  exact hn.trans (by linarith)

private theorem finite_xi_divisor_abs_im_lt (H : ℝ) :
    {p : RiemannXiDivisorZeroIndex | |(riemannXiDivisorZeroValue p).im| < H}.Finite := by
  apply (finite_xi_divisor_abs_im_le H).subset
  intro p hp
  change |(riemannXiDivisorZeroValue p).im| ≤ H
  exact (show |(riemannXiDivisorZeroValue p).im| < H from hp).le

/-- The finite low-zero index set uses a strict cutoff to complement a closed tail. -/
def xiLowHeightIndices (H : ℝ) : Finset RiemannXiDivisorZeroIndex :=
  (finite_xi_divisor_abs_im_lt H).toFinset

/-- Membership does not drop multiplicities or zeros just below the cutoff. -/
@[simp] theorem mem_xiLowHeightIndices (H : ℝ) (p : RiemannXiDivisorZeroIndex) :
    p ∈ xiLowHeightIndices H ↔ |(riemannXiDivisorZeroValue p).im| < H := by
  simp [xiLowHeightIndices]

/-- The actual finite real reciprocal mass below a height cutoff. -/
def xiLowReciprocalMass (H : ℝ) : ℝ :=
  ∑ p ∈ xiLowHeightIndices H, (1 / riemannXiDivisorZeroValue p).re

/-- The finite low-height sum agrees with the corresponding divisor subtype series. -/
theorem xiLowReciprocalMass_eq_tsum (H : ℝ) :
    xiLowReciprocalMass H =
      ∑' p : {p : RiemannXiDivisorZeroIndex // |(riemannXiDivisorZeroValue p).im| < H},
        (1 / riemannXiDivisorZeroValue p.1).re := by
  let e := Equiv.subtypeEquivRight (mem_xiLowHeightIndices H)
  calc
    _ = ∑' p : {p : RiemannXiDivisorZeroIndex // p ∈ xiLowHeightIndices H},
        (1 / riemannXiDivisorZeroValue p.1).re :=
      ((xiLowHeightIndices H).tsum_subtype (fun p => (1 / riemannXiDivisorZeroValue p).re)).symm
    _ = _ := e.tsum_eq (fun p => (1 / riemannXiDivisorZeroValue p.1).re)

/-- Every real reciprocal atom is nonnegative on the actual xi divisor. -/
theorem re_xi_divisor_reciprocal_nonneg (p : RiemannXiDivisorZeroIndex) :
    0 ≤ (1 / riemannXiDivisorZeroValue p).re := by
  rw [one_div, inv_re]
  exact div_nonneg
    (riemannXi_zero_mem_critical_strip (riemannXiDivisorZeroValue_eq_zero p)).1 (normSq_nonneg _)

/-- An exact closed-tail mass identity with a genuinely finite, strict low-height subtraction. -/
theorem tsum_xi_reciprocal_height_tail_eq (H : ℝ) :
    (∑' p : {p : RiemannXiDivisorZeroIndex // H ≤ |(riemannXiDivisorZeroValue p).im|},
      (1 / riemannXiDivisorZeroValue p.1).re) =
      (2 + Real.eulerMascheroniConstant - Real.log (4 * π)) / 2 - xiLowReciprocalMass H := by
  have hs := summable_re_xi_divisor_reciprocal.tsum_subtype_add_tsum_subtype_compl
    {p : RiemannXiDivisorZeroIndex | |(riemannXiDivisorZeroValue p).im| < H}
  have ht := re_logDeriv_riemannXi_zero_eq_neg_tsum_reciprocal
  rw [re_logDeriv_riemannXi_zero_eq] at ht
  rw [xiLowReciprocalMass_eq_tsum]
  change (∑' p : {p : RiemannXiDivisorZeroIndex // |(riemannXiDivisorZeroValue p).im| < H},
      (1 / riemannXiDivisorZeroValue p.1).re) +
    (∑' p : {p : RiemannXiDivisorZeroIndex // ¬ |(riemannXiDivisorZeroValue p).im| < H},
      (1 / riemannXiDivisorZeroValue p.1).re) = _ at hs
  have hpred : (fun p : RiemannXiDivisorZeroIndex => ¬ |(riemannXiDivisorZeroValue p).im| < H) =
      (fun p => H ≤ |(riemannXiDivisorZeroValue p).im|) := funext (fun _ => propext not_lt)
  rw [hpred] at hs
  linarith only [hs, ht]

/-- The remaining reciprocal mass after the finite subtraction is nonnegative. -/
theorem xiLowReciprocalMass_le_total (H : ℝ) :
    xiLowReciprocalMass H ≤ (2 + Real.eulerMascheroniConstant - Real.log (4 * π)) / 2 := by
  have hn : 0 ≤ ∑' p : {p : RiemannXiDivisorZeroIndex //
      H ≤ |(riemannXiDivisorZeroValue p).im|}, (1 / riemannXiDivisorZeroValue p.1).re :=
    tsum_nonneg (fun p => re_xi_divisor_reciprocal_nonneg p.1)
  rw [tsum_xi_reciprocal_height_tail_eq] at hn
  linarith

/-- A finite subset supplies a lower bound without exhaustive low-zero enumeration. -/
theorem sum_reciprocal_le_xiLowReciprocalMass (H : ℝ) (S : Finset RiemannXiDivisorZeroIndex)
    (hS : ∀ p ∈ S, |(riemannXiDivisorZeroValue p).im| < H) :
    (∑ p ∈ S, (1 / riemannXiDivisorZeroValue p).re) ≤ xiLowReciprocalMass H := by
  apply Finset.sum_le_sum_of_subset_of_nonneg
    (fun p hp => (mem_xiLowHeightIndices H p).mpr (hS p hp))
  intro p _ _
  exact re_xi_divisor_reciprocal_nonneg p

end

end PrimeFactorUnimodality
