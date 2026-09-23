import PrimeFactorUnimodality.Helpers.Analytic.TuringCountPhase
import PrimeFactorUnimodality.Helpers.Analytic.XiCountingIntegral
import PrimeFactorUnimodality.Helpers.Analytic.XiHadamardIntegral

/-! # Integrating the actual counting argument across exceptional heights

The ordinates of xi divisor labels are countable. Away from this null set,
the closed count equals the strict count and the exact contour argument
equals the count minus its smooth phase. This proves integrability without
assuming that an entire interval avoids zero ordinates. The remaining
Littlewood identity must identify the argument integral with horizontal
log-modulus endpoint integrals; it is not asserted here.
-/

namespace PrimeFactorUnimodality

noncomputable section

open Complex MeasureTheory Set

/-- Almost every height avoids every xi zero, including all multiplicity labels. -/
theorem ae_xi_horizontal_nonzero :
    ∀ᵐ T : ℝ, ∀ z : ℂ, z.im = T → riemannXi z ≠ 0 := by
  have he : ∀ᵐ T : ℝ, ∀ p : RiemannXiDivisorZeroIndex,
      T ≠ (riemannXiDivisorZeroValue p).im :=
    ae_all_iff.mpr (fun p => volume.ae_ne _)
  filter_upwards [he] with T hT
  intro z hz hzero
  obtain ⟨p, hp⟩ := exists_xi_divisor_index_of_zero hzero
  exact hT p (by rw [hp, hz])

/-- At a regular height, strict and closed counts agree exactly, not just in the limit. -/
theorem xiZeroCount_eq_strict_of_regular {T : ℝ}
    (htop : ∀ z : ℂ, z.im = T → riemannXi z ≠ 0) :
    xiZeroCount T = xiStrictZeroCount T := by
  have he : xiPositiveHeightIndices T = xiStrictPositiveHeightIndices T := by
    ext p
    rw [mem_xiPositiveHeightIndices, mem_xiStrictPositiveHeightIndices]
    constructor
    · rintro ⟨hpos, hle⟩
      exact ⟨hpos, lt_of_le_of_ne hle (fun hp =>
        htop _ hp (riemannXiDivisorZeroValue_eq_zero p))⟩
    · rintro ⟨hpos, hlt⟩
      exact ⟨hpos, hlt.le⟩
  exact congrArg Finset.card he

/-- The contour argument is the actual closed count minus its phase almost everywhere. -/
theorem ae_turingZetaArgument_eq_count_sub_phase {σ : ℝ} (hσ : 1 < σ) :
    ∀ᵐ T : ℝ, 0 < T →
      turingZetaArgument σ T = Real.pi * (xiZeroCount T : ℝ) - turingCountingPhase T := by
  filter_upwards [ae_xi_horizontal_nonzero] with T htop hT
  rw [xiZeroCount_eq_strict_of_regular htop, xiStrictZeroCount_eq_zeta_N]
  linarith [pi_mul_zeta_N_eq_turingArgument_add_phase hσ hT htop]

/-- The argument is integrable across zero ordinates, without a regularity assumption on endpoints. -/
theorem intervalIntegrable_turingZetaArgument {σ a b : ℝ} (hσ : 1 < σ)
    (ha : 0 < a) (hab : a ≤ b) :
    IntervalIntegrable (turingZetaArgument σ) volume a b := by
  apply (((intervalIntegrable_xiZeroCount a b).const_mul Real.pi).sub
    (intervalIntegrable_turingCountingPhase ha hab)).congr_ae
  filter_upwards [ae_restrict_mem measurableSet_uIoc,
    ae_restrict_of_ae (ae_turingZetaArgument_eq_count_sub_phase hσ)] with T hT he
  rw [uIoc_of_le hab] at hT
  exact (he (ha.trans hT.1)).symm

/-- Integrating the normalized contour recovers the complete multiplicity-counted integral. -/
theorem integral_turingZetaArgument_eq_count_sub_phase {σ a b : ℝ} (hσ : 1 < σ)
    (ha : 0 < a) (hab : a ≤ b) :
    (∫ T in a..b, turingZetaArgument σ T) =
      Real.pi * (∫ T in a..b, (xiZeroCount T : ℝ)) - ∫ T in a..b, turingCountingPhase T := by
  have he : (∫ T in a..b, turingZetaArgument σ T) =
      ∫ T in a..b, (Real.pi * (xiZeroCount T : ℝ) - turingCountingPhase T) := by
    apply intervalIntegral.integral_congr_ae
    filter_upwards [ae_turingZetaArgument_eq_count_sub_phase hσ] with T hT hmem
    rw [uIoc_of_le hab] at hmem
    exact hT (ha.trans hmem.1)
  rw [he, intervalIntegral.integral_sub ((intervalIntegrable_xiZeroCount a b).const_mul Real.pi)
    (intervalIntegrable_turingCountingPhase ha hab), intervalIntegral.integral_const_mul]

/-- The discrepancy used by finite zero completeness has its exact phase correction. -/
theorem pi_mul_integral_xiZeroCountingRemainder {σ a b : ℝ} (hσ : 1 < σ)
    (ha : 0 < a) (hab : a ≤ b) :
    Real.pi * (∫ T in a..b, xiZeroCountingRemainder T) =
      (∫ T in a..b, turingZetaArgument σ T) + (∫ T in a..b, turingCountingPhase T) -
        Real.pi * (xiZeroCountingMainIntegral b - xiZeroCountingMainIntegral a) := by
  rw [integral_xiZeroCountingRemainder ha hab,
    integral_turingZetaArgument_eq_count_sub_phase hσ ha hab]
  ring

end

end PrimeFactorUnimodality
