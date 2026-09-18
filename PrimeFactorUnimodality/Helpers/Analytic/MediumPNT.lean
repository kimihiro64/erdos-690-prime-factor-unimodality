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

theorem exists_hasPsiLogFourthError_of_mediumPNT :
    ∃ Y : Real, HasPsiLogFourthError (1 / 2) Y := by
  obtain ⟨c, hc, hbigO⟩ := hasPsiLogRpowBigO_of_mediumPNT
  exact exists_hasPsiLogFourthError_of_logRpowBigO_of_pos_coefficient
    (D := (1 : Real) / 2) (by norm_num) hbigO

end
end PrimeFactorUnimodality
