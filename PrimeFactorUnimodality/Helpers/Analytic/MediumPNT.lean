import PrimeNumberTheoremAnd.MediumPNT
import PrimeFactorUnimodality.Helpers.Analytic.DecayToLogFourth

set_option autoImplicit false

namespace PrimeFactorUnimodality

noncomputable section

open Filter Set
open Asymptotics

/-! The source-level medium prime number theorem supplies the decay needed by the
quantitative log-fourth interface.  The conversion below is deliberately carried
out here: the imported theorem is the analytic proof, while this theorem matches
its signed error term to the absolute-value interface used by the project. -/
theorem hasPsiLogRpowBigO_of_mediumPNT :
    ∃ c : Real, 0 < c ∧ HasPsiLogRpowBigO c ((1 : Real) / 10) := by
  obtain ⟨c, hc, hmedium⟩ := MediumPNT
  refine ⟨c, hc, ?_⟩
  change (fun x : Real => |Chebyshev.psi x - x|) =O[atTop]
    (fun x : Real => x * Real.exp (-c * (Real.log x) ^ ((1 : Real) / 10)))
  rw [isBigO_iff] at hmedium ⊢
  obtain ⟨K, hK⟩ := hmedium
  obtain ⟨T, hT⟩ := eventually_atTop.1 hK
  refine ⟨K, ?_⟩
  filter_upwards [eventually_ge_atTop (max T 2)] with x hx
  have hxT : T ≤ x := le_trans (le_max_left T 2) hx
  have hx2 : (2 : Real) ≤ x := le_trans (le_max_right T 2) hx
  have hx0 : 0 ≤ x := by linarith
  have hsource := hT x hxT
  simpa [Real.norm_eq_abs, Function.id_def, norm_sub, norm_mul,
    Real.norm_of_nonneg hx0, abs_of_nonneg (Real.exp_pos _).le] using hsource

/-! Keep the source theorem available in the quantitative decay interface as
well.  This is the form used when an eventual estimate must be transported
through another analytic argument; it avoids re-opening the asymptotic
normalization at each use site. -/
theorem exists_hasPsiLogRpowDecay_of_mediumPNT :
    ∃ C c α X : Real, 0 ≤ C ∧ 0 < c ∧ 0 < α ∧
      HasPsiLogRpowDecay C c α X := by
  obtain ⟨c, hc, hbigO⟩ := hasPsiLogRpowBigO_of_mediumPNT
  obtain ⟨C, X, hC, hX, hdecay⟩ :=
    exists_hasPsiLogRpowDecay_of_isBigO hbigO
  exact ⟨C, c, (1 : Real) / 10, X, hC, hc, by norm_num, hdecay⟩

theorem exists_hasPsiLogFourthError_of_mediumPNT :
    ∃ Y : Real, HasPsiLogFourthError (1 / 2) Y := by
  obtain ⟨c, _, hbigO⟩ := hasPsiLogRpowBigO_of_mediumPNT
  exact exists_hasPsiLogFourthError_of_logRpowBigO_of_pos_coefficient
    (D := (1 : Real) / 2) (by norm_num) hbigO

/-! The eventual cutoff can be raised to the paper's analytic cutoff without
changing the proved error estimate.  This is the form consumed by the
Dusart tail interfaces. -/
theorem exists_hasPsiLogFourthError_of_mediumPNT_at_paper_cutoff :
    ∃ X : Real, (4e18 : Real) ≤ X ∧
      (42 : Real) ≤ Real.log X ∧ HasPsiLogFourthError (1 / 2) X := by
  obtain ⟨Y, hY⟩ := exists_hasPsiLogFourthError_of_mediumPNT
  let X : Real := max (4e18 : Real) Y
  have hX : (4e18 : Real) ≤ X := le_max_left _ _
  have hYX : Y ≤ X := le_max_right _ _
  have hlogX : (42 : Real) ≤ Real.log X := by
    have hlog_mono : Real.log (4e18 : Real) ≤ Real.log X :=
      Real.log_le_log (by norm_num) hX
    linarith [forty_two_lt_log_four_e18]
  refine ⟨X, hX, hlogX, ?_⟩
  intro x hx
  exact hY x (hYX.trans hx)

theorem exists_hasPsiLogFourthError_of_mediumPNT_at_large_cutoff :
    ∃ X : Real, (4e18 : Real) ≤ X ∧
      (100 : Real) ≤ Real.log X ∧ HasPsiLogFourthError (1 / 2) X := by
  obtain ⟨Y, hY⟩ := exists_hasPsiLogFourthError_of_mediumPNT
  let X : Real := max (4e18 : Real) (max (Real.exp 100) Y)
  have hX : (4e18 : Real) ≤ X := le_max_left _ _
  have hexp : Real.exp 100 ≤ X :=
    le_trans (le_max_left (Real.exp 100) Y) (le_max_right (4e18 : Real) _)
  have hYX : Y ≤ X :=
    le_trans (le_max_right (Real.exp 100) Y) (le_max_right (4e18 : Real) _)
  have hlogX : (100 : Real) ≤ Real.log X := by
    exact (Real.le_log_iff_exp_le (by positivity)).2 hexp
  refine ⟨X, hX, hlogX, ?_⟩
  intro x hx
  exact hY x (hYX.trans hx)

/-! The prime-power correction is also available at the same eventual cutoff.
This records the theta estimate supplied by the source-level PNT without
turning the fixed finite Dusart verification into an assumption. -/
theorem exists_hasThetaLogFourthError_of_mediumPNT_at_large_cutoff :
    ∃ X : Real, (4e18 : Real) ≤ X ∧
      (100 : Real) ≤ Real.log X ∧
      HasThetaLogFourthError (648 / 1000 : Real) X := by
  obtain ⟨X, hX, hlogX, hpsi⟩ :=
    exists_hasPsiLogFourthError_of_mediumPNT_at_large_cutoff
  refine ⟨X, hX, hlogX, ?_⟩
  exact hasThetaLogFourthError_of_psiLogFourthError_sharp hX hpsi

end
end PrimeFactorUnimodality
