import PrimeFactorUnimodality.Helpers.Analytic.DecayToLogFourth
import PrimeFactorUnimodality.Helpers.Analytic.ExplicitPrimeCounting
import PrimeFactorUnimodality.Helpers.Analytic.ExplicitThetaBounds
import PrimeFactorUnimodality.Helpers.Analytic.ExplicitMediumPNT

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
  obtain ⟨c, hc, hmedium⟩ := explicitMediumPNT
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
  simpa [Real.norm_eq_abs, Function.id_def, norm_mul,
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

/-! The decay interface now has a direct theta-error consumer.  This theorem
keeps the coefficient supplied by the source-level PNT existential, while
making the explicit prime-power correction and the published cutoff visible
in one kernel-checked result. -/
theorem exists_hasThetaLogFourthError_of_mediumPNT_via_decay :
    ∃ C Y : Real, 0 ≤ C ∧ (4e18 : Real) ≤ Y ∧
      HasThetaLogFourthError (C + 1) Y := by
  obtain ⟨C, c, α, X, hC, hc, hα, hdecay⟩ :=
    exists_hasPsiLogRpowDecay_of_mediumPNT
  obtain ⟨Y, hXY, h4Y, htheta⟩ :=
    exists_hasThetaLogFourthError_of_psiLogRpowDecay
      hC hc hα hdecay
  exact ⟨C, Y, hC, h4Y, htheta⟩

theorem exists_hasPsiLogFourthError_of_mediumPNT :
    ∃ Y : Real, HasPsiLogFourthError (1 / 2) Y := by
  obtain ⟨c, hc, hbigO⟩ := hasPsiLogRpowBigO_of_mediumPNT
  exact exists_hasPsiLogFourthError_of_logRpowBigO_of_pos_coefficient
    (D := (1 : Real) / 2) (by norm_num) hc (by norm_num) hbigO

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
  refine ⟨Y, hX₀Y, h4Y, ?_⟩
  convert hasThetaLogFourthError_of_psiLogFourthError_sharp h4Y hpsi using 1
  norm_num

/-! The same result in the explicit tail-interface type consumed by the
all-`k` cutoff assembly.  The two predicates have the same pointwise
content, but keeping this coercion named prevents later proofs from silently
confusing a finite-below-cutoff estimate with an unbounded tail estimate. -/
theorem exists_hasThetaLogFourthErrorAbove_of_mediumPNT_above (X₀ : Real) :
    ∃ X : Real, X₀ ≤ X ∧ (4e18 : Real) ≤ X ∧
      HasThetaLogFourthErrorAbove (648 / 1000 : Real) X := by
  obtain ⟨X, hX₀, h4X, htheta⟩ :=
    exists_hasThetaLogFourthError_of_mediumPNT_above X₀
  exact ⟨X, hX₀, h4X, htheta⟩

/-! The same source proof supplies the published Dusart theta inequalities on
the unbounded tail.  This conversion is entirely elementary once the
log-fourth error is available; finite theta endpoint rows are not used here. -/
theorem exists_hasDusartSymmetricThetaBoundsAbove_of_mediumPNT_above
    (X₀ : Real) :
    ∃ X : Real, X₀ ≤ X ∧ (4e18 : Real) ≤ X ∧
      HasDusartSymmetricThetaBoundsAbove X := by
  obtain ⟨X, hX₀, h4X, htheta⟩ :=
    exists_hasThetaLogFourthErrorAbove_of_mediumPNT_above X₀
  have hXpos : 0 < X := by linarith
  have hlogX : (42 : Real) ≤ Real.log X := by
    have hlog_mono : Real.log (4e18 : Real) ≤ Real.log X :=
      Real.log_le_log (by norm_num) h4X
    linarith [forty_two_lt_log_four_e18]
  have hA : (648 / 1000 : Real) / Real.log X ≤
      (12167 / 500000 : Real) := by
    have hlogXpos : 0 < Real.log X := by linarith
    apply (div_le_iff₀ hlogXpos).2
    nlinarith
  exact ⟨X, hX₀, h4X,
    hasDusartSymmetricThetaBoundsAbove_of_logFourthError
      hXpos (by linarith) (by norm_num) hA htheta⟩

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

/-! The source-level PNT only has to handle the unbounded tail.  Once a
finite computation supplies the interval estimate through any cutoff above
`89693`, this glues it to the PNT tail and produces the exact global
log-cubed statement used by the all-`k` reduction. -/
theorem hasLogCubedShortIntervalPrime_of_finite_and_mediumPNT
    {X₀ : Real} (hX₀ : (89693 : Real) ≤ X₀)
    (finite : ∀ X : Real, X₀ ≤ X →
      HasLogCubedShortIntervalPrimeBelow X) :
    HasLogCubedShortIntervalPrime := by
  obtain ⟨X, hX₀X, _, tail⟩ :=
    exists_dusartPrimeInInterval_of_mediumPNT X₀
  have finiteX : HasLogCubedShortIntervalPrimeBelow X :=
    finite X hX₀X
  exact hasLogCubedShortIntervalPrime_of_below_and_above (hX₀.trans hX₀X)
    finiteX (fun x hx => by
      obtain ⟨q, hq, hxq, hupper⟩ := tail x hx
      refine ⟨q, hq, hxq, ?_⟩
      convert hupper using 1 <;> ring)

/-! If the source theorem supplies an explicit upper bound for its eventual
cutoff, one finite table at that upper bound is enough.  This is the form
used by a bounded computational provider: the table is not duplicated for
each existential cutoff chosen by the asymptotic argument. -/
theorem hasLogCubedShortIntervalPrime_of_finite_and_bounded_mediumPNT
    {X₀ B : Real} (hX₀ : (89693 : Real) ≤ X₀)
    (hXB : X₀ ≤ B)
    (finite : HasLogCubedShortIntervalPrimeBelow B)
    (tail : ∃ X : Real, X₀ ≤ X ∧ X ≤ B ∧
      (∀ x : Real, X ≤ x →
        ∃ q : Nat, q.Prime ∧ x < q ∧
          (q : Real) ≤ x + x / (Real.log x) ^ 3)) :
    HasLogCubedShortIntervalPrime := by
  obtain ⟨X, hX₀X, hXB', htail⟩ := tail
  apply hasLogCubedShortIntervalPrime_of_below_and_above (hX₀.trans hXB) finite
  intro x hx
  exact htail x (hXB'.trans hx)

/-! The existential form is the minimal selected-cutoff contract.  It is
strictly weaker than asking a finite provider to answer at every possible
cutoff: the source theorem chooses one cutoff, and one finite verification is
then consumed at exactly that cutoff. -/
theorem hasLogCubedShortIntervalPrime_of_selected_finite_and_mediumPNT
    {X₀ : Real} (hX₀ : (89693 : Real) ≤ X₀)
    (selected : ∃ X : Real, X₀ ≤ X ∧
      HasLogCubedShortIntervalPrimeBelow X ∧
      (∀ x : Real, X ≤ x →
        ∃ q : Nat, q.Prime ∧ x < q ∧
          (q : Real) ≤ x + x / (Real.log x) ^ 3)) :
    HasLogCubedShortIntervalPrime := by
  obtain ⟨X, hX₀X, finite, tail⟩ := selected
  exact hasLogCubedShortIntervalPrime_of_below_and_above
    (hX₀.trans hX₀X) finite tail

theorem hasDusartShortIntervalPrime_of_finite_and_mediumPNT
    {X₀ : Real} (hX₀ : (89693 : Real) ≤ X₀)
    (finiteDusart : HasDusartShortIntervalPrimeBelow (89693 : Real))
    (finiteLogCubed : ∀ X : Real, X₀ ≤ X →
      HasLogCubedShortIntervalPrimeBelow X) :
    HasDusartShortIntervalPrime := by
  exact hasDusartShortIntervalPrime_of_below_and_logCubed
    finiteDusart
    (hasLogCubedShortIntervalPrime_of_finite_and_mediumPNT hX₀
      finiteLogCubed)

/-! The combined short-interval interface also has a selected-cutoff form.
Only one finite log-cubed verification, at the cutoff selected by the
analytic tail theorem, is needed; no provider quantified over all possible
cutoffs is required. -/
theorem hasDusartShortIntervalPrime_of_selected_finite_and_mediumPNT
    {X₀ : Real} (hX₀ : (89693 : Real) ≤ X₀)
    (finiteDusart : HasDusartShortIntervalPrimeBelow (89693 : Real))
    (selected : ∃ X : Real, X₀ ≤ X ∧
      HasLogCubedShortIntervalPrimeBelow X ∧
      (∀ x : Real, X ≤ x →
        ∃ q : Nat, q.Prime ∧ x < q ∧
          (q : Real) ≤ x + x / (Real.log x) ^ 3)) :
    HasDusartShortIntervalPrime := by
  obtain ⟨X, hX₀X, finiteLogCubed, tail⟩ := selected
  exact hasDusartShortIntervalPrime_of_below_and_logCubed
    finiteDusart
    (hasLogCubedShortIntervalPrime_of_selected_finite_and_mediumPNT
      hX₀ ⟨X, hX₀X, finiteLogCubed, tail⟩)

/-! The source-level PNT also supplies the published prime-counting tail once
the finite Abel-summation core is bounded.  The core is transported to the
raised cutoff by the proved monotonicity estimate; no prime-counting theorem
is imported at this boundary. -/
theorem exists_hasDusartPublishedPrimeCountingBoundsAbove_of_mediumPNT_and_core
    {X C : Real} (hX : (4e18 : Real) ≤ X)
    (hC0 : 0 ≤ C) (hC : C ≤ 3 / 5)
    (hcore : ∀ Y : Real, X ≤ Y →
      |primeCountingCore Y| ≤ C * Y / Real.log Y ^ 4) :
    ∃ Y : Real, X ≤ Y ∧
      HasDusartPublishedPrimeCountingBoundsAbove Y := by
  obtain ⟨Y, hXY, h4Y, htheta⟩ :=
    exists_hasThetaLogFourthError_of_mediumPNT_above X
  have hXpos : 0 < X := by linarith
  have hYpos : 0 < Y := lt_of_lt_of_le hXpos hXY
  have hlogX : (42 : Real) ≤ Real.log X :=
    forty_two_lt_log_four_e18.le.trans
      (Real.log_le_log (by norm_num) hX)
  have hX1 : 1 < X := by
    exact (Real.log_pos_iff hXpos.le).mp (by linarith)
  have hlogY : (42 : Real) ≤ Real.log Y := by
    exact hlogX.trans (Real.log_le_log hXpos hXY)
  have hcoreY : |primeCountingCore Y| ≤ C * Y / Real.log Y ^ 4 :=
    hcore Y hXY
  have hAsym : HasDusartPrimeCountingAsymptoticAbove Y :=
    hasDusartPrimeCountingAsymptoticAbove_of_core_and_theta_error
      hYpos (by linarith [hlogY]) (by norm_num) (by norm_num)
      hC0 hC hlogY hcoreY htheta
  exact ⟨Y, hXY, hasDusartPublishedPrimeCountingBoundsAbove_of_asymptotic_from
    hYpos (by linarith [hlogY]) hAsym⟩

theorem exists_hasDusartRealPrimeCountingBoundsAbove_of_mediumPNT_and_core
    {X C : Real} (hX : (4e18 : Real) ≤ X)
    (hC0 : 0 ≤ C) (hC : C ≤ 3 / 5)
    (hcore : ∀ Y : Real, X ≤ Y →
      |primeCountingCore Y| ≤ C * Y / Real.log Y ^ 4) :
    ∃ Y : Real, X ≤ Y ∧
      HasDusartRealPrimeCountingBoundsAbove Y := by
  obtain ⟨Y, hXY, h4Y, htheta⟩ :=
    exists_hasThetaLogFourthError_of_mediumPNT_above X
  have hXpos : 0 < X := by linarith
  have hX1 : 1 < X := by
    have hlogX : (42 : Real) ≤ Real.log X :=
      forty_two_lt_log_four_e18.le.trans
        (Real.log_le_log (by norm_num) hX)
    exact (Real.log_pos_iff hXpos.le).mp (by linarith)
  have hlogX : (42 : Real) ≤ Real.log X :=
    forty_two_lt_log_four_e18.le.trans
      (Real.log_le_log (by norm_num) hX)
  have hcoreY : |primeCountingCore Y| ≤ C * Y / Real.log Y ^ 4 :=
    hcore Y hXY
  have hlogY : (42 : Real) ≤ Real.log Y :=
    hlogX.trans (Real.log_le_log hXpos hXY)
  have hYpos : 0 < Y := lt_of_lt_of_le hXpos hXY
  have hbounds : HasDusartRealPrimeCountingBoundsAbove Y :=
    hasDusartRealPrimeCountingBoundsAbove_of_core_and_theta_error
      hYpos (by linarith [hlogY]) le_rfl
      (by norm_num) (by norm_num) hC0 hC hlogY hcoreY htheta
  exact ⟨Y, hXY, hbounds⟩

/-! A single common raised cutoff packages the two unbounded Dusart inputs
used by the all-`k` tail: published prime counting and prime selection. -/
theorem exists_mediumPNT_dusart_tail_inputs
    {X C : Real} (hX : (4e18 : Real) ≤ X)
    (hC0 : 0 ≤ C) (hC : C ≤ 3 / 5)
    (hcore : ∀ Y : Real, X ≤ Y →
      |primeCountingCore Y| ≤ C * Y / Real.log Y ^ 4) :
    ∃ Y : Real, X ≤ Y ∧
      HasDusartPublishedPrimeCountingBoundsAbove Y ∧
      (∀ x : Real, Y ≤ x →
        ∃ q : Nat, q.Prime ∧ x < q ∧
          (q : Real) ≤ x * (1 + 1 / (Real.log x) ^ 3)) := by
  obtain ⟨Y, hXY, hpublished⟩ :=
    exists_hasDusartPublishedPrimeCountingBoundsAbove_of_mediumPNT_and_core
      hX hC0 hC hcore
  obtain ⟨Z, hYZ, h4Z, htheta⟩ :=
    exists_hasThetaLogFourthError_of_mediumPNT_above Y
  have hZpos : 0 < Z := by linarith [hX]
  have hlogZ : (10 : Real) < Real.log Z := by
    have hlog4 : (42 : Real) ≤ Real.log Z :=
      forty_two_lt_log_four_e18.le.trans
        (Real.log_le_log (by norm_num) h4Z)
    linarith
  have hpublishedZ : HasDusartPublishedPrimeCountingBoundsAbove Z := by
    constructor <;> intro x hx
    · exact hpublished.1 x (hYZ.trans hx)
    · exact hpublished.2 x (hYZ.trans hx)
  refine ⟨Z, hXY.trans hYZ, hpublishedZ, ?_⟩
  exact dusartPrimeInInterval_of_logFourthError_from
    hZpos (by linarith) hlogZ (by norm_num) (by
      have hlog4 : (42 : Real) ≤ Real.log Z :=
        forty_two_lt_log_four_e18.le.trans
          (Real.log_le_log (by norm_num) h4Z)
      have hlogpos : 0 < Real.log Z := by linarith
      apply (div_le_iff₀ hlogpos).2
      nlinarith [hlog4]) htheta

/-! A single raised cutoff can carry both analytic tail facts in the exact
forms consumed by the all-`k` assembly.  The prime-counting estimate is first
obtained at the core-dependent cutoff, then transported to the later cutoff
chosen for prime selection. -/
theorem exists_mediumPNT_real_dusart_tail_inputs
    {X C : Real} (hX : (4e18 : Real) ≤ X)
    (hC0 : 0 ≤ C) (hC : C ≤ 3 / 5)
    (hcore : ∀ Y : Real, X ≤ Y →
      |primeCountingCore Y| ≤ C * Y / Real.log Y ^ 4) :
    ∃ Y : Real, X ≤ Y ∧
      HasDusartRealPrimeCountingBoundsAbove Y ∧
      (∀ x : Real, Y ≤ x →
        ∃ q : Nat, q.Prime ∧ x < q ∧
          (q : Real) ≤ x * (1 + 1 / (Real.log x) ^ 3)) := by
  obtain ⟨Y, hXY, hprime⟩ :=
    exists_hasDusartRealPrimeCountingBoundsAbove_of_mediumPNT_and_core
      hX hC0 hC hcore
  obtain ⟨Z, hYZ, h4Z, hinterval⟩ :=
    exists_dusartPrimeInInterval_of_mediumPNT Y
  refine ⟨Z, hXY.trans hYZ, ?_, hinterval⟩
  constructor
  · intro x hx
    exact hprime.1 x (hYZ.trans hx)
  · intro x hx
    exact hprime.2 x (hYZ.trans hx)

/-! Complete source-level tail package.  This is the exact analytic shape
needed to glue finite cutoff tables to the unbounded all-`k` argument; it
contains no finite computation and imports no Dusart proposition. -/
theorem exists_mediumPNT_all_dusart_tail_inputs
    {X C : Real} (hX : (4e18 : Real) ≤ X)
    (hC0 : 0 ≤ C) (hC : C ≤ 3 / 5)
    (hcore : ∀ Y : Real, X ≤ Y →
      |primeCountingCore Y| ≤ C * Y / Real.log Y ^ 4) :
    ∃ Y : Real, X ≤ Y ∧
      HasDusartPublishedPrimeCountingBoundsAbove Y ∧
      HasThetaLogFourthErrorAbove (648 / 1000 : Real) Y ∧
      (∀ x : Real, Y ≤ x →
        ∃ q : Nat, q.Prime ∧ x < q ∧
          (q : Real) ≤ x + x / (Real.log x) ^ 3) := by
  obtain ⟨Y, hXY, hpublished, hinterval⟩ :=
    exists_mediumPNT_dusart_tail_inputs hX hC0 hC hcore
  obtain ⟨Z, hYZ, h4Z, htheta⟩ :=
    exists_hasThetaLogFourthError_of_mediumPNT_above Y
  refine ⟨Z, hXY.trans hYZ, ?_, htheta, ?_⟩
  · constructor
    · intro x hx
      exact hpublished.1 x (hYZ.trans hx)
    · intro x hx
      exact hpublished.2 x (hYZ.trans hx)
  · intro x hx
    obtain ⟨q, hq, hxq, hupper⟩ := hinterval x (hYZ.trans hx)
    exact ⟨q, hq, hxq, by convert hupper using 1 <;> ring⟩

/-! The tail package with the theta estimate already converted to the exact
Dusart inequality.  This is still source-level work: the only finite input
remaining for the final global theorem is the bounded prefix. -/
theorem exists_mediumPNT_all_dusart_tail_inputs_with_theta_bounds
    {X C : Real} (hX : (4e18 : Real) ≤ X)
    (hC0 : 0 ≤ C) (hC : C ≤ 3 / 5)
    (hcore : ∀ Y : Real, X ≤ Y →
      |primeCountingCore Y| ≤ C * Y / Real.log Y ^ 4) :
    ∃ Y : Real, X ≤ Y ∧
      HasDusartPublishedPrimeCountingBoundsAbove Y ∧
      HasDusartSymmetricThetaBoundsAbove Y ∧
      HasThetaLogFourthErrorAbove (648 / 1000 : Real) Y ∧
      (∀ x : Real, Y ≤ x →
        ∃ q : Nat, q.Prime ∧ x < q ∧
          (q : Real) ≤ x + x / (Real.log x) ^ 3) := by
  obtain ⟨Y, hXY, hpublished, htheta, hinterval⟩ :=
    exists_mediumPNT_all_dusart_tail_inputs hX hC0 hC hcore
  have hYpos : 0 < Y := by linarith [hX]
  have hlogY : (42 : Real) ≤ Real.log Y := by
    have hlog_mono : Real.log (4e18 : Real) ≤ Real.log Y :=
      Real.log_le_log (by norm_num) (hX.trans hXY)
    linarith [forty_two_lt_log_four_e18]
  have hthetaBounds := hasDusartSymmetricThetaBoundsAbove_of_logFourthError
    hYpos (by linarith) (by norm_num)
    (by
      have hlogYpos : 0 < Real.log Y := by linarith
      apply (div_le_iff₀ hlogYpos).2
      nlinarith)
    htheta
  exact ⟨Y, hXY, hpublished, hthetaBounds, htheta, hinterval⟩

/-! The Abel core is not an additional analytic assumption.  Once the finite
theta remainder is supplied below the chosen cutoff, the explicit integral
estimate proves the core budget, and the source-level PNT supplies every
unbounded Dusart input.  This is the non-certificate bridge used by the
eventual all-`k` assembly. -/
theorem exists_mediumPNT_all_dusart_tail_inputs_of_finite_theta_error
    {A X : Real} (hX : (4e18 : Real) ≤ X)
    (hA0 : 0 ≤ A) (hA1 : A ≤ 1)
    (finiteThetaError : ∀ Y : Real, X ≤ Y →
      HasThetaLogFourthErrorBelow A Y) :
    ∃ Y : Real, X ≤ Y ∧
      HasDusartPublishedPrimeCountingBoundsAbove Y ∧
      HasThetaLogFourthErrorAbove (648 / 1000 : Real) Y ∧
      (∀ x : Real, Y ≤ x →
        ∃ q : Nat, q.Prime ∧ x < q ∧
          (q : Real) ≤ x + x / (Real.log x) ^ 3) := by
  have hcore : ∀ Y : Real, X ≤ Y →
      |primeCountingCore Y| ≤ (3 / 5 : Real) * Y / Real.log Y ^ 4 := by
    intro Y hXY
    exact primeCountingCore_abs_le_at_large_cutoff_of_theta_error
      (hX.trans hXY) hA0 hA1 (finiteThetaError Y hXY)
  exact exists_mediumPNT_all_dusart_tail_inputs hX (by norm_num) (by norm_num)
    hcore

/-! The same finite-theta reduction in the real prime-counting interface used
by the cutoff assembly.  This is kept separate from the preceding published
form so callers do not have to re-prove the monotone conversion from the
source-level Abel estimate to the real-variable inequalities. -/
theorem exists_mediumPNT_all_real_dusart_tail_inputs_of_finite_theta_error
    {A X : Real} (hX : (4e18 : Real) ≤ X)
    (hA0 : 0 ≤ A) (hA1 : A ≤ 1)
    (finiteThetaError : ∀ Y : Real, X ≤ Y →
      HasThetaLogFourthErrorBelow A Y) :
    ∃ Y : Real, X ≤ Y ∧
      HasDusartRealPrimeCountingBoundsAbove Y ∧
      HasThetaLogFourthErrorAbove (648 / 1000 : Real) Y ∧
      (∀ x : Real, Y ≤ x →
        ∃ q : Nat, q.Prime ∧ x < q ∧
          (q : Real) ≤ x + x / (Real.log x) ^ 3) := by
  have hcore : ∀ Y : Real, X ≤ Y →
      |primeCountingCore Y| ≤ (3 / 5 : Real) * Y / Real.log Y ^ 4 := by
    intro Y hXY
    exact primeCountingCore_abs_le_at_large_cutoff_of_theta_error
      (hX.trans hXY) hA0 hA1 (finiteThetaError Y hXY)
  obtain ⟨Y, hXY, _, htheta⟩ :=
    exists_hasThetaLogFourthError_of_mediumPNT_above X
  obtain ⟨Z, hYZ, hreal, hintervalZ⟩ :=
    exists_mediumPNT_real_dusart_tail_inputs hX (by norm_num) (by norm_num)
      hcore
  refine ⟨max Y Z, hXY.trans (le_max_left _ _), ?_, ?_, ?_⟩
  · constructor
    · intro x hx
      exact hreal.1 x (le_trans (le_max_right Y Z) hx)
    · intro x hx
      exact hreal.2 x (le_trans (le_max_right Y Z) hx)
  · intro x hx
    exact htheta x (le_trans (le_max_left Y Z) hx)
  · intro x hx
    obtain ⟨q, hq, hxq, hupper⟩ :=
      hintervalZ x (le_trans (le_max_right Y Z) hx)
    exact ⟨q, hq, hxq, by convert hupper using 1 <;> ring⟩

/-! The complete real-variable tail package used by the all-`k` assembly.
All unbounded estimates are transported to one common raised cutoff. -/
theorem exists_mediumPNT_all_real_dusart_tail_inputs_with_theta_bounds
    {A X : Real} (hX : (4e18 : Real) ≤ X)
    (hA0 : 0 ≤ A) (hA1 : A ≤ 1)
    (finiteThetaError : ∀ Y : Real, X ≤ Y →
      HasThetaLogFourthErrorBelow A Y) :
    ∃ Y : Real, X ≤ Y ∧
      HasDusartRealPrimeCountingBoundsAbove Y ∧
      HasDusartSymmetricThetaBoundsAbove Y ∧
      HasThetaLogFourthErrorAbove (648 / 1000 : Real) Y ∧
      (∀ x : Real, Y ≤ x →
        ∃ q : Nat, q.Prime ∧ x < q ∧
          (q : Real) ≤ x + x / (Real.log x) ^ 3) := by
  obtain ⟨Y, hXY, hreal, htheta, hinterval⟩ :=
    exists_mediumPNT_all_real_dusart_tail_inputs_of_finite_theta_error
      hX hA0 hA1 finiteThetaError
  have hYpos : 0 < Y := by linarith [hX]
  have hlogY : (42 : Real) ≤ Real.log Y := by
    have hlog_mono : Real.log (4e18 : Real) ≤ Real.log Y :=
      Real.log_le_log (by norm_num) (hX.trans hXY)
    linarith [forty_two_lt_log_four_e18]
  have hthetaBounds := hasDusartSymmetricThetaBoundsAbove_of_logFourthError
    hYpos (by linarith) (by norm_num)
    (by
      have hlogYpos : 0 < Real.log Y := by linarith
      apply (div_le_iff₀ hlogYpos).2
      nlinarith [hlogY]) htheta
  exact ⟨Y, hXY, hreal, hthetaBounds, htheta, hinterval⟩

end
end PrimeFactorUnimodality
