import PrimeNumberTheoremAnd.MediumPNT
import PrimeFactorUnimodality.Helpers.Analytic.DecayToLogFourth
import PrimeFactorUnimodality.Helpers.Analytic.ExplicitPrimeCounting

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

/-! The cutoff can be raised past any externally chosen analytic threshold.
Keeping this general avoids baking the paper's numerical cutoff into the
source-level PNT adapter. -/
theorem exists_hasPsiLogFourthError_of_mediumPNT_above (X₀ : Real) :
    ∃ X : Real, X₀ ≤ X ∧ HasPsiLogFourthError (1 / 2) X := by
  obtain ⟨Y, hY⟩ := exists_hasPsiLogFourthError_of_mediumPNT
  let X : Real := max X₀ Y
  refine ⟨X, le_max_left _ _, ?_⟩
  intro x hx
  exact hY x ((le_max_right X₀ Y).trans hx)

/-! A general theta version of the preceding adapter.  The cutoff is raised
past both the caller's threshold and the point where the sharp elementary
prime-power correction is valid. -/
theorem exists_hasThetaLogFourthError_of_mediumPNT_above (X₀ : Real) :
    ∃ X : Real, X₀ ≤ X ∧ (4e18 : Real) ≤ X ∧
      HasThetaLogFourthError (648 / 1000 : Real) X := by
  obtain ⟨Y, hY, hpsi⟩ :=
    exists_hasPsiLogFourthError_of_mediumPNT_above (max X₀ (4e18 : Real))
  have hX₀Y : X₀ ≤ Y := (le_max_left _ _).trans hY
  have h4Y : (4e18 : Real) ≤ Y := (le_max_right _ _).trans hY
  exact ⟨Y, hX₀Y, h4Y,
    hasThetaLogFourthError_of_psiLogFourthError_sharp h4Y hpsi⟩

/-! The eventual cutoff can be raised to the paper's analytic cutoff without
changing the proved error estimate.  This is the form consumed by the
Dusart tail interfaces. -/
theorem exists_hasPsiLogFourthError_of_mediumPNT_at_paper_cutoff :
    ∃ X : Real, (4e18 : Real) ≤ X ∧
      (42 : Real) ≤ Real.log X ∧ HasPsiLogFourthError (1 / 2) X := by
  obtain ⟨Y, hY, herror⟩ :=
    exists_hasPsiLogFourthError_of_mediumPNT_above (4e18 : Real)
  let X : Real := max (4e18 : Real) Y
  have hX : (4e18 : Real) ≤ X := le_max_left _ _
  have hYX : Y ≤ X := le_max_right _ _
  have hlogX : (42 : Real) ≤ Real.log X := by
    have hlog_mono : Real.log (4e18 : Real) ≤ Real.log X :=
      Real.log_le_log (by norm_num) hX
    linarith [forty_two_lt_log_four_e18]
  refine ⟨X, hX, hlogX, ?_⟩
  exact fun x hx => herror x (hYX.trans hx)

theorem exists_hasPsiLogFourthError_of_mediumPNT_at_large_cutoff :
    ∃ X : Real, (4e18 : Real) ≤ X ∧
      (100 : Real) ≤ Real.log X ∧ HasPsiLogFourthError (1 / 2) X := by
  obtain ⟨Y, hY, herror⟩ :=
    exists_hasPsiLogFourthError_of_mediumPNT_above (max (4e18 : Real) (Real.exp 100))
  let X : Real := max (4e18 : Real) (max (Real.exp 100) Y)
  have hX : (4e18 : Real) ≤ X := le_max_left _ _
  have hexp : Real.exp 100 ≤ X :=
    le_trans (le_max_left (Real.exp 100) Y) (le_max_right (4e18 : Real) _)
  have hYX : Y ≤ X :=
    le_trans (le_max_right (Real.exp 100) Y) (le_max_right (4e18 : Real) _)
  have hlogX : (100 : Real) ≤ Real.log X := by
    exact (Real.le_log_iff_exp_le (by positivity)).2 hexp
  refine ⟨X, hX, hlogX, ?_⟩
  exact fun x hx => herror x (hYX.trans hx)

/-! The prime-power correction is also available at the same eventual cutoff.
This records the theta estimate supplied by the source-level PNT without
turning the fixed finite Dusart verification into an assumption. -/
theorem exists_hasThetaLogFourthError_of_mediumPNT_at_large_cutoff :
    ∃ X : Real, (4e18 : Real) ≤ X ∧
      (100 : Real) ≤ Real.log X ∧
      HasThetaLogFourthError (648 / 1000 : Real) X := by
  obtain ⟨X, hX, h4X, htheta⟩ :=
    exists_hasThetaLogFourthError_of_mediumPNT_above
      (max (4e18 : Real) (Real.exp 100))
  have hexp : Real.exp 100 ≤ X := by
    exact (le_max_right (4e18 : Real) (Real.exp 100)).trans hX
  have hlogX : (100 : Real) ≤ Real.log X := by
    exact (Real.le_log_iff_exp_le (by positivity)).2 hexp
  exact ⟨X, h4X, hlogX, htheta⟩

/-! The same eventual theta estimate yields the logarithm-cubed prime interval
needed by the tail argument.  This is the analytic half only; the finite
interval range remains a separate computational input. -/
theorem exists_dusartPrimeInInterval_of_mediumPNT
    (X₀ : Real) :
    ∃ X : Real, X₀ ≤ X ∧ (4e18 : Real) ≤ X ∧
      (∀ x : Real, X ≤ x →
        ∃ q : Nat, q.Prime ∧ x < q ∧
          (q : Real) ≤ x * (1 + 1 / (Real.log x) ^ 3)) := by
  obtain ⟨X, hX₀, h4X, htheta⟩ :=
    exists_hasThetaLogFourthError_of_mediumPNT_above X₀
  have hXpos : 0 < X := by linarith
  have hlogX : (10 : Real) < Real.log X := by
    have hlog4 : (42 : Real) ≤ Real.log X :=
      forty_two_lt_log_four_e18.le.trans
        (Real.log_le_log (by norm_num) h4X)
    linarith
  refine ⟨X, hX₀, h4X, ?_⟩
  exact dusartPrimeInInterval_of_logFourthError_from
    hXpos (by linarith) hlogX (by norm_num) (by
      have hlog4 : (42 : Real) ≤ Real.log X :=
        forty_two_lt_log_four_e18.le.trans
          (Real.log_le_log (by norm_num) h4X)
      have hlogpos : 0 < Real.log X := by linarith
      apply (div_le_iff₀ hlogpos).2
      nlinarith [hlog4]) htheta

/-! The source-level PNT also supplies the published prime-counting tail once
the finite Abel-summation core is bounded.  The core is transported to the
raised cutoff by the proved monotonicity estimate; no prime-counting theorem
is imported at this boundary. -/
theorem exists_hasDusartPublishedPrimeCountingBoundsAbove_of_mediumPNT_and_core
    {X C : Real} (hX : (4e18 : Real) ≤ X)
    (hC0 : 0 ≤ C) (hC : C ≤ 3 / 5)
    (hcore : |primeCountingCore X| ≤ C * X / Real.log X ^ 4) :
    ∃ Y : Real, X ≤ Y ∧
      HasDusartPublishedPrimeCountingBoundsAbove Y := by
  obtain ⟨Y, hXY, hpsi⟩ :=
    exists_hasPsiLogFourthError_of_mediumPNT_above X
  have hXpos : 0 < X := by linarith
  have hYpos : 0 < Y := lt_of_lt_of_le hXpos hXY
  have hlogX : (42 : Real) ≤ Real.log X :=
    forty_two_lt_log_four_e18.le.trans
      (Real.log_le_log (by norm_num) hX)
  have hX1 : 1 < X := by
    exact (Real.log_pos_iff hXpos.le).mp (by linarith)
  have hlogY : (42 : Real) ≤ Real.log Y := by
    exact hlogX.trans (Real.log_le_log hXpos hXY)
  have hcoreY : |primeCountingCore X| ≤ C * Y / Real.log Y ^ 4 :=
    primeCountingCore_scale_le hX1 hXY (by linarith [hlogX]) hC0 hcore
  have htheta : HasThetaLogFourthError (648 / 1000 : Real) Y :=
    hasThetaLogFourthError_of_psiLogFourthError_sharp (hX.trans hXY) hpsi
  have hAsym : HasDusartPrimeCountingAsymptoticAbove Y :=
    hasDusartPrimeCountingAsymptoticAbove_of_core_and_theta_error
      hYpos (by linarith [hlogY]) (by norm_num) (by norm_num)
      hC0 hC hlogY hcoreY htheta
  exact ⟨Y, hXY, hasDusartPublishedPrimeCountingBoundsAbove_of_asymptotic_from
    hYpos (by linarith [hlogY]) hAsym⟩

end
end PrimeFactorUnimodality
