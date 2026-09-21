import PrimeFactorUnimodality.Helpers.Analytic.DecayToLogFourth
import PrimeFactorUnimodality.Helpers.Analytic.DusartProof
import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows
import PrimeFactorUnimodality.Helpers.Analytic.MediumPNT
import PrimeFactorUnimodality.Helpers.Analytic.ZetaExplicitBounds

set_option autoImplicit false

namespace PrimeFactorUnimodality

noncomputable section

/-!
# Closed explicit theta estimates

Implementation owner: Luna.

This module must prove and export
`PrimeFactorUnimodality.wangCrapis_thetaBounds : HasDusartThetaBounds`
from the repository's proved zero-free-region, Chebyshev, logarithm-envelope,
and compact finite low-endpoint machinery.  It must not import a prepackaged
Dusart theorem or add an assumption-backed provider.

The exact proof obligations and dependency order are recorded in
`LEAN_COMPLETION_HANDOFF.md`.  The finite singleton seed below is closed; it
does not claim to be the global provider.
-/

/-! Closed singleton seed for the finite theta assembler. -/
theorem wangCrapis_thetaPrefix :
    HasDusartSymmetricThetaBoundsBelow (2 : Real) := by
  exact hasDusartSymmetricThetaBoundsBelow_mono (by norm_num)
    (hasDusartSymmetricThetaBoundsBelow_of_endpoint_rows
      dusartThetaEndpointRow_three_cover)

theorem wangCrapis_thetaPrefix_three :
    HasDusartSymmetricThetaBoundsBelow (3 : Real) := by
  exact hasDusartSymmetricThetaBoundsBelow_of_endpoint_rows
    dusartThetaEndpointRow_three_cover

theorem wangCrapis_thetaBounds_lower_2_3
    {x : Real} (hx : 2 < x) (hx3 : x ≤ 3) :
    x * (1 - (12323 / 10000 : Real) / Real.log x) <
      Chebyshev.theta x := by
  have hxpos : 0 < x := by linarith
  have hfloor : ⌊x⌋₊ = 2 := by
    have hlo : 2 ≤ ⌊x⌋₊ := Nat.le_floor (le_of_lt hx)
    have hhi : ⌊x⌋₊ ≤ 2 := Nat.floor_le_of_le hx3
    omega
  have htheta : Chebyshev.theta x = Real.log 2 := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hfloor, theta_two_eq_log_two]
  rw [htheta]
  have hlogpos : 0 < Real.log x := Real.log_pos (by linarith)
  have hlog_le : Real.log x ≤ Real.log 3 :=
    Real.log_le_log hxpos hx3
  have hlog_lt : Real.log x < (12323 : Real) / 10000 := by
    have hthree : Real.log 3 < (11 : Real) / 10 := by
      exact Real.log_three_lt_d9
    linarith
  have hcoef : 1 - (12323 / 10000 : Real) / Real.log x < 0 := by
    apply sub_neg.mpr
    apply (lt_div_iff₀ hlogpos).2
    linarith
  have hleft : x * (1 - (12323 / 10000 : Real) / Real.log x) < 0 :=
    mul_neg_of_pos_of_neg hxpos hcoef
  have hlog2pos : 0 < Real.log (2 : Real) := Real.log_pos (by norm_num)
  linarith

theorem wangCrapis_thetaBounds_upper_0_3
    {x : Real} (hx : 0 < x) (hx3 : x ≤ 3) :
    Chebyshev.theta x - x < x / 36260 := by
  have htheta_nonneg : 0 ≤ Chebyshev.theta x := Chebyshev.theta_nonneg x
  by_cases hlt : x < 2
  · rw [Chebyshev.theta_eq_zero_of_lt_two hlt]
    positivity
  · have htheta_le : Chebyshev.theta x ≤ Chebyshev.theta 3 :=
      Chebyshev.theta_mono hx3
    have htheta3 : Chebyshev.theta (3 : Real) =
        Real.log 2 + Real.log 3 := by
      have hsum := Chebyshev.theta_eq_sum_primesLE_log 3
      have hp : Nat.primesLE 3 = {2, 3} := by decide
      rw [hp] at hsum
      simpa using hsum
    rw [htheta3] at htheta_le
    have hlog2lt : Real.log (2 : Real) < 1 := by
      nlinarith [Real.log_two_lt_d9]
    have hlog3lt : Real.log (3 : Real) < (11 : Real) / 10 :=
      Real.log_three_lt_d9
    have hright : 0 < x / 36260 := by positivity
    linarith

theorem wangCrapis_thetaBoundsBelow_3 :
    HasDusartSymmetricThetaBoundsBelow (3 : Real) := by
  constructor
  · intro x hx hx3
    exact wangCrapis_thetaBounds_upper_0_3 hx hx3
  · intro x hx hx3
    exact wangCrapis_thetaBounds_lower_2_3 hx hx3

/-! The same direct low-endpoint computation supplies the strict prefix used
    by the Schoenfeld split. -/
theorem wangCrapis_strictThetaPrefix_three :
    HasStrictThetaUpperBelow (3 : Real) := by
  intro x hx hx3
  by_cases hsmall : x < 2
  · rw [Chebyshev.theta_eq_zero_of_lt_two hsmall]
    linarith
  · have htheta_le : Chebyshev.theta x ≤ Chebyshev.theta 3 :=
      Chebyshev.theta_mono hx3
    have htheta3 : Chebyshev.theta (3 : Real) =
        Real.log 2 + Real.log 3 := by
      have hsum := Chebyshev.theta_eq_sum_primesLE_log 3
      have hp : Nat.primesLE 3 = {2, 3} := by decide
      rw [hp] at hsum
      simpa using hsum
    rw [htheta3] at htheta_le
    have hlog2lt : Real.log (2 : Real) < (9 : Real) / 10 :=
      Real.log_two_lt_d9
    have hlog3lt : Real.log (3 : Real) < (11 : Real) / 10 :=
      Real.log_three_lt_d9
    linarith

/-! The fixed explicit-formula input is exported at the theta boundary so the
    eventual psi/theta tail proof consumes the constructed estimate rather than
    the package's existential placeholder. -/
theorem wangCrapis_explicit_log_derivative_input :
    ∃ A C : Real, 0 < C ∧ A ∈ Ioc 0 (1 / 2) ∧
      LogDerivZetaHasBound A C := by
  obtain ⟨A, C, hC, hA, hbound, _⟩ :=
    zetaLogDeriv_explicit_bounded_and_holo
  exact ⟨A, C, hC, hA, hbound⟩

theorem wangCrapis_theta_upper_e28_from_paper_inputs
    {x : Real} (hx : (8e11 : Real) ≤ x)
    (hx_exp : x ≤ Real.exp 28)
    (hpsi_error : |Chebyshev.psi x - x| ≤
      (2841 : Real) / 100000000 * x)
    (hgap : (9999 : Real) / 10000 * Real.sqrt x ≤
      Chebyshev.psi x - Chebyshev.theta x) :
    Chebyshev.theta x - x ≤ x / 36260 := by
  exact dusart_theta_upper_e28_from_absolute_psi_error
    hx hx_exp hpsi_error hgap

theorem wangCrapis_theta_upper_e28_from_strict_paper_inputs
    {x : Real} (hx : (8e11 : Real) ≤ x)
    (hx_exp : x ≤ Real.exp 28)
    (hpsi : Chebyshev.psi x <
      (100002841 : Real) / 100000000 * x)
    (hgap : (9999 : Real) / 10000 * Real.sqrt x <
      Chebyshev.psi x - Chebyshev.theta x) :
    Chebyshev.theta x - x < x / 36260 := by
  exact dusart_theta_upper_e28_step_strict hx hx_exp hpsi hgap

/-! Paper-facing Proposition 5.1 assembler.  The three hypotheses correspond
to Dusart's finite table, middle explicit psi estimate, and large-range theta
estimate; none of the range-specific obligations is hidden in this glue. -/
theorem dusart_proposition_5_1_of_paper_ranges
    (finite : ∀ x : Real, 0 < x → x ≤ (8e11 : Real) →
      Chebyshev.theta x - x < x / 36260)
    (middle : ∀ x : Real, (8e11 : Real) ≤ x →
      x ≤ Real.exp 28 →
      |Chebyshev.psi x - x| < (2841 : Real) / 100000000 * x ∧
      (9999 : Real) / 10000 * Real.sqrt x <
        Chebyshev.psi x - Chebyshev.theta x)
    (tail : ∀ x : Real, Real.exp 28 ≤ x →
      Chebyshev.theta x - x < x / 36260) :
    ∀ x : Real, 0 < x →
      Chebyshev.theta x - x < x / 36260 := by
  intro x hx
  by_cases hfinite : x ≤ (8e11 : Real)
  · exact finite x hx hfinite
  by_cases hmiddle : x ≤ Real.exp 28
  · obtain ⟨herror, hgap⟩ := middle x (le_of_not_ge hfinite) hmiddle
    have hpsi : Chebyshev.psi x <
        (100002841 : Real) / 100000000 * x := by
      have hupper := (abs_lt.mp herror).2
      nlinarith
    exact dusart_theta_upper_e28_step_strict
      (le_of_not_ge hfinite) hmiddle hpsi hgap
  · exact tail x (le_of_not_ge hmiddle)

/-! Translate the paper's one-sided Proposition 5.1 estimate together with
its independent lower estimate into the exact theta-provider interface. -/
theorem wangCrapis_thetaBounds_of_paper_upper_and_lower
    (upper : ∀ x : Real, 0 < x →
      Chebyshev.theta x - x < x / 36260)
    (lower : ∀ x : Real, 2 < x →
      x * (1 - (12323 / 10000 : Real) / Real.log x) <
        Chebyshev.theta x) :
    HasDusartThetaBounds := by
  constructor
  · intro x hx
    have h := upper x hx
    nlinarith
  · exact lower

theorem wangCrapis_thetaBounds_of_paper_ranges
    (finite : ∀ x : Real, 0 < x → x ≤ (8e11 : Real) →
      Chebyshev.theta x - x < x / 36260)
    (middle : ∀ x : Real, (8e11 : Real) ≤ x →
      x ≤ Real.exp 28 →
      |Chebyshev.psi x - x| < (2841 : Real) / 100000000 * x ∧
      (9999 : Real) / 10000 * Real.sqrt x <
        Chebyshev.psi x - Chebyshev.theta x)
    (tail : ∀ x : Real, Real.exp 28 ≤ x →
      Chebyshev.theta x - x < x / 36260)
    (lower : ∀ x : Real, 2 < x →
      x * (1 - (12323 / 10000 : Real) / Real.log x) <
        Chebyshev.theta x) :
    HasDusartThetaBounds := by
  apply wangCrapis_thetaBounds_of_paper_upper_and_lower
  · exact dusart_proposition_5_1_of_paper_ranges finite middle tail
  · exact lower

/-! The large-range clause in Proposition 5.1 follows directly from the
explicit logarithm-fourth error once its cutoff is placed at `exp 28`. -/
theorem dusart_proposition_5_1_tail_of_logFourthError
    {A : Real}
    (hA_nonneg : 0 ≤ A)
    (hA : A / Real.log (Real.exp 28) ≤ 12167 / 500000)
    (thetaError : HasThetaLogFourthErrorAbove A (Real.exp 28)) :
    ∀ x : Real, Real.exp 28 ≤ x →
      Chebyshev.theta x - x < x / 36260 := by
  have hlog : (10 : Real) < Real.log (Real.exp 28) := by
    rw [Real.log_exp]
    norm_num
  have tail : HasDusartSymmetricThetaBoundsAbove (Real.exp 28) :=
    hasDusartSymmetricThetaBoundsAbove_of_logFourthError
      (by positivity) hlog hA_nonneg hA thetaError
  exact tail.1

/-! Paper-facing Proposition 5.1 assembly with the large-range analytic input
made explicit at its actual `exp 28` cutoff. -/
theorem wangCrapis_thetaBounds_of_paper_ranges_and_logFourthTail
    (finite : ∀ x : Real, 0 < x → x ≤ (8e11 : Real) →
      Chebyshev.theta x - x < x / 36260)
    (middle : ∀ x : Real, (8e11 : Real) ≤ x →
      x ≤ Real.exp 28 →
      |Chebyshev.psi x - x| < (2841 : Real) / 100000000 * x ∧
      (9999 : Real) / 10000 * Real.sqrt x <
        Chebyshev.psi x - Chebyshev.theta x)
    (lower : ∀ x : Real, 2 < x →
      x * (1 - (12323 / 10000 : Real) / Real.log x) <
        Chebyshev.theta x)
    {A : Real}
    (hA_nonneg : 0 ≤ A)
    (hA : A / Real.log (Real.exp 28) ≤ 12167 / 500000)
    (thetaError : HasThetaLogFourthErrorAbove A (Real.exp 28)) :
    HasDusartThetaBounds := by
  exact wangCrapis_thetaBounds_of_paper_ranges finite middle
    (dusart_proposition_5_1_tail_of_logFourthError
      hA_nonneg hA thetaError) lower

/-! The middle-range gap in Proposition 5.1 is supplied by Proposition 3.1.
Its bounded verification remains a separate finite obligation; the analytic
tail and the conversion from the paper's `psi` error are assembled here. -/
theorem wangCrapis_thetaBounds_of_paper_ranges_and_prop31
    (finite : ∀ x : Real, 0 < x → x ≤ (8e11 : Real) →
      Chebyshev.theta x - x < x / 36260)
    (middlePsi : ∀ x : Real, (8e11 : Real) ≤ x →
      x ≤ Real.exp 28 →
      |Chebyshev.psi x - x| < (2841 : Real) / 100000000 * x)
    (finiteGap : ∀ x : Real, (121 : Real) < x →
      x < (4e18 : Real) ^ 2 →
      (9999 : Real) / 10000 * Real.sqrt x <
        Chebyshev.psi x - Chebyshev.theta x)
    {A : Real}
    (hA_nonneg : 0 ≤ A)
    (hA : A / Real.log (Real.exp 28) ≤ 12167 / 500000)
    (thetaError : HasThetaLogFourthErrorAbove A (Real.exp 28))
    (lower : ∀ x : Real, 2 < x →
      x * (1 - (12323 / 10000 : Real) / Real.log x) <
        Chebyshev.theta x) :
    HasDusartThetaBounds := by
  apply wangCrapis_thetaBounds_of_paper_ranges_and_logFourthTail
    finite
  · intro x hx hx_exp
    refine ⟨middlePsi x hx hx_exp, ?_⟩
    apply finiteGap x (by linarith)
    calc
      x ≤ Real.exp 28 := hx_exp
      _ < (1446257067000 : Real) := exp_twentyEight_lt_dusart_endpoint
      _ < (4e18 : Real) ^ 2 := by norm_num
  · exact lower
  · exact hA_nonneg
  · exact hA
  · exact thetaError

/-! A single published-size error input supplies both analytic tails: its
`exp 28` instance feeds Proposition 5.1, while monotonicity of the cutoff
feeds the square-root argument in Proposition 3.1. -/
theorem wangCrapis_thetaBounds_of_paper_ranges_and_prop31_thetaError
    (finite : ∀ x : Real, 0 < x → x ≤ (8e11 : Real) →
      Chebyshev.theta x - x < x / 36260)
    (middlePsi : ∀ x : Real, (8e11 : Real) ≤ x →
      x ≤ Real.exp 28 →
      |Chebyshev.psi x - x| < (2841 : Real) / 100000000 * x)
    (finiteGap : ∀ x : Real, (121 : Real) < x →
      x < (4e18 : Real) ^ 2 →
      (9999 : Real) / 10000 * Real.sqrt x <
        Chebyshev.psi x - Chebyshev.theta x)
    (thetaError : HasThetaLogFourthErrorAbove
      (648 / 1000 : Real) (Real.exp 28))
    (lower : ∀ x : Real, 2 < x →
      x * (1 - (12323 / 10000 : Real) / Real.log x) <
        Chebyshev.theta x) :
    HasDusartThetaBounds := by
  have hA : (648 / 1000 : Real) / Real.log (Real.exp 28) ≤
      12167 / 500000 := by
    rw [Real.log_exp]
    norm_num
  have hcut : Real.exp 28 ≤ (4e18 : Real) := by
    calc
      Real.exp 28 < (1446257067000 : Real) :=
        exp_twentyEight_lt_dusart_endpoint
      _ ≤ (4e18 : Real) := by norm_num
  have thetaErrorLarge : HasThetaLogFourthErrorAbove
      (648 / 1000 : Real) (4e18 : Real) := by
    exact hasThetaLogFourthErrorAbove_mono hcut thetaError
  have prop31 : ∀ x : Real, (121 : Real) < x →
      (9999 : Real) / 10000 * Real.sqrt x <
        Chebyshev.psi x - Chebyshev.theta x :=
    dusart_proposition_3_1_of_finite_and_thetaErrorAbove
      finiteGap thetaErrorLarge
  apply wangCrapis_thetaBounds_of_paper_ranges
    finite
  · intro x hx hx_exp
    refine ⟨middlePsi x hx hx_exp, ?_⟩
    apply prop31 x
    · linarith
    · calc
        x ≤ Real.exp 28 := hx_exp
        _ < (1446257067000 : Real) :=
          exp_twentyEight_lt_dusart_endpoint
        _ < (4e18 : Real) ^ 2 := by norm_num
  · exact dusart_proposition_5_1_tail_of_logFourthError
      (by norm_num) hA thetaError
  · exact lower

theorem wangCrapis_thetaBounds_of_indexed_prop31_rows_and_thetaError
    {X : Real} {n : Nat}
    (hX : (4e18 : Real) ^ 2 ≤ X)
    (rows : Fin n → DusartProposition31FiniteRow)
    (cover : DusartProposition31FiniteIndexedRowsCover rows X)
    (finite : ∀ x : Real, 0 < x → x ≤ (8e11 : Real) →
      Chebyshev.theta x - x < x / 36260)
    (middlePsi : ∀ x : Real, (8e11 : Real) ≤ x →
      x ≤ Real.exp 28 →
      |Chebyshev.psi x - x| < (2841 : Real) / 100000000 * x)
    (thetaError : HasThetaLogFourthErrorAbove
      (648 / 1000 : Real) (Real.exp 28))
    (lower : ∀ x : Real, 2 < x →
      x * (1 - (12323 / 10000 : Real) / Real.log x) <
        Chebyshev.theta x) :
    HasDusartThetaBounds := by
  apply wangCrapis_thetaBounds_of_paper_ranges_and_prop31_thetaError
    finite middlePsi
  · intro x hx hxc
    exact dusartProposition31Finite_of_indexed_rows cover x hx
      (le_trans (le_of_lt hxc) hX)
  · exact thetaError
  · exact lower

/-! Direct finite-prefix assembly for the provider interface.  The finite
upper and lower estimates are kept as separate obligations, as in the paper;
only the unbounded tail is converted from the explicit error estimate. -/
theorem wangCrapis_thetaBounds_of_paper_finite_prefix_and_logFourthTail
    {A X : Real}
    (hXpos : 0 < X)
    (hlogX : (10 : Real) < Real.log X)
    (finiteUpper : ∀ x : Real, 0 < x → x ≤ X →
      Chebyshev.theta x - x < x / 36260)
    (finiteLower : ∀ x : Real, 2 < x → x ≤ X →
      x * (1 - (12323 / 10000 : Real) / Real.log x) <
        Chebyshev.theta x)
    (hA_nonneg : 0 ≤ A)
    (hA : A / Real.log X ≤ 12167 / 500000)
    (thetaError : HasThetaLogFourthErrorAbove A X) :
    HasDusartThetaBounds := by
  have tail : HasDusartSymmetricThetaBoundsAbove X :=
    hasDusartSymmetricThetaBoundsAbove_of_logFourthError
      hXpos hlogX hA_nonneg hA thetaError
  constructor
  · intro x hx
    by_cases hsmall : x ≤ X
    · have h := finiteUpper x hx hsmall
      nlinarith
    · have h := tail.1 x (le_of_not_ge hsmall)
      nlinarith
  · intro x hx
    by_cases hsmall : x ≤ X
    · exact finiteLower x hx hsmall
    · have hlog_pos : 0 < Real.log x := Real.log_pos (by linarith)
      have hlow := (abs_lt.mp (tail.2 x hx (le_of_not_ge hsmall))).1
      have htarget :
          x * (1 - (12323 / 10000 : Real) / Real.log x) =
            x - (12323 / 10000 : Real) * x / Real.log x := by
        field_simp [hlog_pos.ne']
      rw [htarget]
      linarith

/-! Specialization at the cutoff used in Dusart's Proposition 5.1. -/
theorem wangCrapis_thetaBounds_of_paper_finite_exp28
    (finiteUpper : ∀ x : Real, 0 < x → x ≤ Real.exp 28 →
      Chebyshev.theta x - x < x / 36260)
    (finiteLower : ∀ x : Real, 2 < x → x ≤ Real.exp 28 →
      x * (1 - (12323 / 10000 : Real) / Real.log x) <
        Chebyshev.theta x)
    (thetaError : HasThetaLogFourthErrorAbove
      (648 / 1000 : Real) (Real.exp 28)) :
    HasDusartThetaBounds := by
  apply wangCrapis_thetaBounds_of_paper_finite_prefix_and_logFourthTail
    (X := Real.exp 28) (A := (648 / 1000 : Real))
    (Real.exp_pos 28)
  · rw [Real.log_exp]
    norm_num
  · exact finiteUpper
  · exact finiteLower
  · norm_num
  · rw [Real.log_exp]
    norm_num
  · exact thetaError

/-! Global Proposition 5.1 in the three ranges used by Dusart: the finite
Table 6.4 range, the explicit middle range ending at `exp 28`, and the
large-range theta-error tail. -/
theorem dusart_proposition_5_1_of_three_ranges
    (finite : ∀ x : Real, 0 < x →
      x ≤ (8e11 : Real) →
      Chebyshev.theta x - x < x / 36260)
    (middle : ∀ x : Real, (8e11 : Real) ≤ x →
      x ≤ Real.exp 28 →
      Chebyshev.theta x - x < x / 36260)
    (tail : ∀ x : Real, Real.exp 28 ≤ x →
      Chebyshev.theta x - x < x / 36260) :
    ∀ x : Real, 0 < x →
      Chebyshev.theta x - x < x / 36260 := by
  intro x hx
  by_cases hfinite : x ≤ (8e11 : Real)
  · exact finite x hx hfinite
  · by_cases hmiddle : x ≤ Real.exp 28
    · exact middle x (le_of_not_ge hfinite) hmiddle
    · exact tail x (le_of_not_ge hmiddle)

/-! The finite part of the paper's Table 6.4 is represented by compact indexed
endpoint rows. The assembler proves both theta inequalities on every real
point covered by those rows, including points between consecutive endpoints. -/
theorem wangCrapis_thetaBounds_of_indexed_endpoint_rows_and_tail
    {A X : Real} {n : Nat}
    (hXpos : 0 < X) (hlogX : (10 : Real) < Real.log X)
    (rows : Fin n → DusartThetaEndpointRow)
    (cover : DusartThetaEndpointIndexedCoverUpTo rows X)
    (hA_nonneg : 0 ≤ A)
    (hA : A / Real.log X ≤ 12167 / 500000)
    (thetaError : HasThetaLogFourthError A X) :
    HasDusartThetaBounds := by
  exact wangCrapis_thetaBounds_of_logFourthTail hXpos hlogX
    (hasDusartSymmetricThetaBoundsBelow_of_indexed_endpoint_rows cover)
    hA_nonneg hA thetaError

/-! The same boundary consumes compact endpoint chunks directly.  This keeps
    the generated finite table independent of the analytic tail proof. -/
theorem wangCrapis_thetaBounds_of_endpoint_chunks_and_tail
    {A : Real} (first : DusartThetaEndpointChunk)
    (rest : List DusartThetaEndpointChunk)
    (hXpos : 0 <
      (DusartThetaEndpointChunk.appendMany first rest).cutoff)
    (hlogX : (10 : Real) < Real.log
      (DusartThetaEndpointChunk.appendMany first rest).cutoff)
    (hA_nonneg : 0 ≤ A)
    (hA : A / Real.log
      (DusartThetaEndpointChunk.appendMany first rest).cutoff ≤
      12167 / 500000)
    (thetaError : HasThetaLogFourthError A
      (DusartThetaEndpointChunk.appendMany first rest).cutoff) :
    HasDusartThetaBounds := by
  exact wangCrapis_thetaBounds_of_logFourthTail hXpos hlogX
    (hasDusartSymmetricThetaBoundsBelow_of_endpoint_chunks first rest)
    hA_nonneg hA thetaError

theorem wangCrapis_thetaBounds_of_prefix_and_endpoint_chunks_and_tail
    {A x₀ : Real} (hx₀ : (2 : Real) ≤ x₀)
    (prefix : HasDusartSymmetricThetaBoundsBelow x₀)
    (first : DusartThetaEndpointChunk)
    (rest : List DusartThetaEndpointChunk)
    (hcutoff : x₀ ≤
      (DusartThetaEndpointChunk.appendMany first rest).cutoff)
    (hXpos : 0 <
      (DusartThetaEndpointChunk.appendMany first rest).cutoff)
    (hlogX : (10 : Real) < Real.log
      (DusartThetaEndpointChunk.appendMany first rest).cutoff)
    (hA_nonneg : 0 ≤ A)
    (hA : A / Real.log
      (DusartThetaEndpointChunk.appendMany first rest).cutoff ≤
      12167 / 500000)
    (thetaError : HasThetaLogFourthError A
      (DusartThetaEndpointChunk.appendMany first rest).cutoff) :
    HasDusartThetaBounds := by
  exact wangCrapis_thetaBounds_of_logFourthTail hXpos hlogX
    (hasDusartSymmetricThetaBoundsBelow_of_indexed_prefix_and_endpoint_rows
      hx₀ prefix
      (by
        intro x hx hX
        obtain ⟨i, hleft, hright⟩ :=
          (DusartThetaEndpointChunk.appendMany first rest).cover x
            (hx₀.trans hx) hX
        exact ⟨i, hleft, hright⟩))
    hA_nonneg hA thetaError

/-! Paper-facing form when a separately proved prefix is followed by an
indexed Table 6.4 suffix. -/
theorem wangCrapis_thetaBounds_of_indexed_prefix_endpoint_rows_and_tail
    {A X x₀ : Real} {n : Nat}
    (hXpos : 0 < X) (hlogX : (10 : Real) < Real.log X)
    (hx₀ : (2 : Real) ≤ x₀)
    (prefix : HasDusartSymmetricThetaBoundsBelow x₀)
    (rows : Fin n → DusartThetaEndpointRow)
    (cover : DusartThetaEndpointIndexedCoverFrom rows x₀ X)
    (hA_nonneg : 0 ≤ A)
    (hA : A / Real.log X ≤ 12167 / 500000)
    (thetaError : HasThetaLogFourthError A X) :
    HasDusartThetaBounds := by
  exact wangCrapis_thetaBounds_of_logFourthTail hXpos hlogX
    (hasDusartSymmetricThetaBoundsBelow_of_indexed_prefix_and_endpoint_rows
      hx₀ prefix cover)
    hA_nonneg hA thetaError

theorem wangCrapis_large_root_gap_from_strict_theta_error
    {x : Real} (hx : (4e18 : Real) ^ 2 ≤ x)
    (herror : ∀ y : Real, (4e18 : Real) ≤ y →
      |Chebyshev.theta y - y| <
        (648 : Real) / 1000 * y / (Real.log y) ^ 4) :
    (9999 : Real) / 10000 * Real.sqrt x <
      Chebyshev.psi x - Chebyshev.theta x := by
  exact psi_sub_theta_gt_9999_sqrt_of_large_strict_theta_error hx herror

theorem wangCrapis_three_root_upper_gap_strict
    {x : Real} (hx : (121 : Real) ≤ x)
    (h2cut : (4e18 : Real) ≤ x ^ (2 : Real)⁻¹)
    (h3cut : (4e18 : Real) ≤ x ^ (3 : Real)⁻¹)
    (h5cut : (4e18 : Real) ≤ x ^ (5 : Real)⁻¹)
    (h2theta : Chebyshev.theta (x ^ (2 : Real)⁻¹) <
      x ^ (2 : Real)⁻¹ + x ^ (2 : Real)⁻¹ / 36260)
    (h3theta : Chebyshev.theta (x ^ (3 : Real)⁻¹) <
      x ^ (3 : Real)⁻¹ + x ^ (3 : Real)⁻¹ / 36260)
    (h5theta : Chebyshev.theta (x ^ (5 : Real)⁻¹) <
      x ^ (5 : Real)⁻¹ + x ^ (5 : Real)⁻¹ / 36260) :
    Chebyshev.psi x - Chebyshev.theta x <
      (100007 : Real) / 100000 * Real.sqrt x +
        (178 : Real) / 100 * x ^ (1 / 3 : Real) := by
  exact dusart_gap_upper_from_three_strict_large_theta_bounds
    hx h2cut h3cut h5cut h2theta h3theta h5theta

/-! Exact assembly boundary for the theta provider.  The finite endpoint
proof and the explicit log-fourth tail remain separate inputs until both are
proved from their underlying arguments. -/
theorem wangCrapis_thetaBounds_of_logFourthTail
    {A X : Real} (hXpos : 0 < X) (hlogX : (10 : Real) < Real.log X)
    (finite : HasDusartSymmetricThetaBoundsBelow X)
    (hA_nonneg : 0 ≤ A)
    (hA : A / Real.log X ≤ 12167 / 500000)
    (thetaError : HasThetaLogFourthError A X) :
    HasDusartThetaBounds := by
  exact hasDusartThetaBounds_of_finite_and_logFourth_from
    hXpos hlogX finite hA_nonneg hA thetaError

/-! This is the independent theta upper estimate used by Dusart's Lemma 3.3.
It is derived from the finite prefix and the explicit tail directly, rather
than obtained from the final bundled Proposition 5.1 provider. -/
theorem wangCrapis_theta_upper_1000081_of_finite_and_logFourthTail
    {A X : Real} (hXpos : 0 < X) (hlogX : (10 : Real) < Real.log X)
    (finite : HasDusartSymmetricThetaBoundsBelow X)
    (hA_nonneg : 0 ≤ A)
    (hA : A / Real.log X ≤ 12167 / 500000)
    (thetaError : HasThetaLogFourthError A X) :
    ∀ y : Real, 0 < y →
      Chebyshev.theta y < (1000081 : Real) / 1000000 * y := by
  have bounds := wangCrapis_thetaBounds_of_logFourthTail
    hXpos hlogX finite hA_nonneg hA thetaError
  intro y hy
  have hupper := bounds.1 y hy
  nlinarith

/-! Paper-shaped variant: the bounded upper estimate is supplied as
Schoenfeld's strict `theta x < x` prefix, while the bounded lower estimate is
kept as its own finite obligation. -/
theorem wangCrapis_thetaBounds_of_strict_theta_prefix_and_logFourthTail
    {A X : Real} (hXpos : 0 < X) (hlogX : (10 : Real) < Real.log X)
    (upperPrefix : HasStrictThetaUpperBelow X)
    (lower : ∀ x : Real, 2 < x → x ≤ X →
      |Chebyshev.theta x - x| <
        (12323 / 10000 : Real) * x / Real.log x)
    (hA_nonneg : 0 ≤ A)
    (hA : A / Real.log X ≤ 12167 / 500000)
    (thetaError : HasThetaLogFourthError A X) :
    HasDusartThetaBounds := by
  exact wangCrapis_thetaBounds_of_logFourthTail hXpos hlogX
    (hasDusartSymmetricThetaBoundsBelow_of_strict_theta_prefix
      upperPrefix lower)
    hA_nonneg hA thetaError

/-! The paper-shaped split can start with the proved `x ≤ 3` prefix and then
    consume a compact endpoint suffix.  The strict upper margin stays an
    explicit row obligation; the lower estimate remains separate. -/
theorem wangCrapis_thetaBounds_of_strict_prefix_endpoint_rows_and_logFourthTail
    {A X : Real} {n : Nat}
    (hXpos : 0 < X) (hlogX : (10 : Real) < Real.log X)
    (rows : Fin n → DusartThetaEndpointRow)
    (cover : DusartThetaEndpointIndexedCoverFrom rows (3 : Real) X)
    (margin : ∀ i, (rows i).theta_upper < (rows i).left)
    (lower : ∀ x : Real, 2 < x → x ≤ X →
      |Chebyshev.theta x - x| <
        (12323 / 10000 : Real) * x / Real.log x)
    (hA_nonneg : 0 ≤ A)
    (hA : A / Real.log X ≤ 12167 / 500000)
    (thetaError : HasThetaLogFourthError A X) :
    HasDusartThetaBounds := by
  apply wangCrapis_thetaBounds_of_strict_theta_prefix_and_logFourthTail
    hXpos hlogX
  · intro x hx hX
    by_cases hsmall : x ≤ (3 : Real)
    · exact wangCrapis_strictThetaPrefix_three x hx hsmall
    · obtain ⟨i, hleft, hright⟩ := cover x (by linarith) hX
      exact strictThetaUpperRow_provides
        ((rows i).toStrictUpperRow (margin i)) hleft hright
  · exact lower
  · exact hA_nonneg
  · exact hA
  · exact thetaError

/-! The lower finite estimate can use the same split.  The direct prefix
    calculation discharges its absolute-error clause, leaving only the
    endpoint suffix as an input. -/
theorem wangCrapis_theta_lower_error_below_three
    {x : Real} (hx : 2 < x) (hx3 : x ≤ 3) :
    |Chebyshev.theta x - x| <
      (12323 / 10000 : Real) * x / Real.log x := by
  have hprefix := wangCrapis_thetaBoundsBelow_3
  have hupper := hprefix.1 x (by linarith) hx3
  have hlower := hprefix.2 x hx hx3
  have hlogpos : 0 < Real.log x := Real.log_pos (by linarith)
  have hlog_le : Real.log x ≤ Real.log 3 :=
    Real.log_le_log (by linarith) hx3
  have hlog3lt : Real.log (3 : Real) < (11 : Real) / 10 :=
    Real.log_three_lt_d9
  have hcoef : (1 : Real) / 36260 <
      (12323 / 10000 : Real) / Real.log x := by
    apply (lt_div_iff₀ hlogpos).2
    nlinarith
  have hscaled := mul_lt_mul_of_pos_right hcoef (by linarith : 0 < x)
  have herror : x / 36260 <
      (12323 / 10000 : Real) * x / Real.log x := by
    nlinarith
  apply (abs_lt).2
  constructor
  · nlinarith
  · exact hupper.trans herror

theorem wangCrapis_thetaBounds_of_strict_prefix_endpoint_rows_and_logFourthTail_of_suffix_lower
    {A X : Real} {n : Nat}
    (hXpos : 0 < X) (hlogX : (10 : Real) < Real.log X)
    (rows : Fin n → DusartThetaEndpointRow)
    (cover : DusartThetaEndpointIndexedCoverFrom rows (3 : Real) X)
    (margin : ∀ i, (rows i).theta_upper < (rows i).left)
    (lowerSuffix : ∀ x : Real, 3 ≤ x → x ≤ X →
      |Chebyshev.theta x - x| <
        (12323 / 10000 : Real) * x / Real.log x)
    (hA_nonneg : 0 ≤ A)
    (hA : A / Real.log X ≤ 12167 / 500000)
    (thetaError : HasThetaLogFourthError A X) :
    HasDusartThetaBounds := by
  apply wangCrapis_thetaBounds_of_strict_prefix_endpoint_rows_and_logFourthTail
    hXpos hlogX rows cover margin
  · intro x hx hX
    by_cases hsmall : x ≤ (3 : Real)
    · exact wangCrapis_theta_lower_error_below_three hx hsmall
    · exact lowerSuffix x (by linarith) hX
  · exact hA_nonneg
  · exact hA
  · exact thetaError

/-! Endpoint rows also carry the lower absolute-error field.  This variant
    derives the suffix lower estimate from those fields, leaving only the
    strict upper margin as the numerical Table 6.4 obligation. -/
theorem wangCrapis_thetaBounds_of_strict_prefix_endpoint_rows_and_logFourthTail_from_rows
    {A X : Real} {n : Nat}
    (hXpos : 0 < X) (hlogX : (10 : Real) < Real.log X)
    (rows : Fin n → DusartThetaEndpointRow)
    (cover : DusartThetaEndpointIndexedCoverFrom rows (3 : Real) X)
    (margin : ∀ i, (rows i).theta_upper < (rows i).left)
    (hA_nonneg : 0 ≤ A)
    (hA : A / Real.log X ≤ 12167 / 500000)
    (thetaError : HasThetaLogFourthError A X) :
    HasDusartThetaBounds := by
  apply wangCrapis_thetaBounds_of_strict_prefix_endpoint_rows_and_logFourthTail_of_suffix_lower
    hXpos hlogX rows cover margin
  · intro x hx hX
    obtain ⟨i, hleft, hright⟩ := cover x (by linarith) hX
    exact (dusartThetaEndpointRow_provides (rows i) hleft hright).lower
      x (by linarith) hleft hright
  · exact hA_nonneg
  · exact hA
  · exact thetaError

/-! Certificate-facing form of the paper split.  The strict Schoenfeld prefix
is supplied as an indexed compact row cover; the lower estimate remains a
separate analytic or finite obligation. -/
theorem wangCrapis_thetaBounds_of_indexed_strict_rows_and_logFourthTail
    {A X : Real} {n : Nat}
    (hXpos : 0 < X) (hlogX : (10 : Real) < Real.log X)
    (rows : Fin n → StrictThetaUpperRow)
    (cover : StrictThetaUpperIndexedCoverUpTo rows X)
    (lower : ∀ x : Real, 2 < x → x ≤ X →
      |Chebyshev.theta x - x| <
        (12323 / 10000 : Real) * x / Real.log x)
    (hA_nonneg : 0 ≤ A)
    (hA : A / Real.log X ≤ 12167 / 500000)
    (thetaError : HasThetaLogFourthError A X) :
    HasDusartThetaBounds := by
  exact wangCrapis_thetaBounds_of_strict_theta_prefix_and_logFourthTail
    hXpos hlogX (hasStrictThetaUpperBelow_of_indexed_rows cover) lower
    hA_nonneg hA thetaError

/-! The verified Table 6.6 representation can feed the same source-level
    theta assembly once its endpoint computation and the lower estimate are
    supplied. -/
theorem wangCrapis_thetaBounds_of_verified_table_rows_and_logFourthTail
    {A X : Real} {rows : List DusartThetaTableVerifiedRow}
    (cover : DusartThetaTableVerifiedRowsCoverUpTo rows X)
    (hXpos : 0 < X) (hlogX : (10 : Real) < Real.log X)
    (hA_nonneg : 0 ≤ A)
    (hA : A / Real.log X ≤ 12167 / 500000)
    (thetaError : HasThetaLogFourthError A X) :
    HasDusartThetaBounds := by
  exact wangCrapis_thetaBounds_of_logFourthTail hXpos hlogX
    (hasDusartSymmetricThetaBoundsBelow_of_verified_table_rows cover)
    hA_nonneg hA thetaError

theorem wangCrapis_thetaBounds_of_verified_table_chunks_and_logFourthTail
    {A : Real} (first : DusartThetaTableVerifiedChunk)
    (rest : List DusartThetaTableVerifiedChunk)
    (hXpos : 0 <
      (DusartThetaTableVerifiedChunk.appendMany first rest).cutoff)
    (hlogX : (10 : Real) < Real.log
      (DusartThetaTableVerifiedChunk.appendMany first rest).cutoff)
    (hA_nonneg : 0 ≤ A)
    (hA : A / Real.log
      (DusartThetaTableVerifiedChunk.appendMany first rest).cutoff ≤
      12167 / 500000)
    (thetaError : HasThetaLogFourthError A
      (DusartThetaTableVerifiedChunk.appendMany first rest).cutoff) :
    HasDusartThetaBounds := by
  exact wangCrapis_thetaBounds_of_logFourthTail hXpos hlogX
    (hasDusartSymmetricThetaBoundsBelow_of_verified_chunks first rest)
    hA_nonneg hA thetaError

theorem wangCrapis_thetaBounds_of_table66_chunks_and_logFourthTail
    {A : Real} (first : DusartThetaTable66Chunk)
    (rest : List DusartThetaTable66Chunk)
    (hXpos : 0 <
      (DusartThetaTable66Chunk.appendMany first rest).cutoff)
    (hlogX : (10 : Real) < Real.log
      (DusartThetaTable66Chunk.appendMany first rest).cutoff)
    (hA_nonneg : 0 ≤ A)
    (hA : A / Real.log
      (DusartThetaTable66Chunk.appendMany first rest).cutoff ≤
      12167 / 500000)
    (thetaError : HasThetaLogFourthError A
      (DusartThetaTable66Chunk.appendMany first rest).cutoff) :
    HasDusartThetaBounds := by
  exact wangCrapis_thetaBounds_of_logFourthTail hXpos hlogX
    (hasDusartSymmetricThetaBoundsBelow_of_table66_chunks first rest)
    hA_nonneg hA thetaError

theorem wangCrapis_theta_upper_1000081_of_table66_chunks_and_logFourthTail
    {A : Real} (first : DusartThetaTable66Chunk)
    (rest : List DusartThetaTable66Chunk)
    (hXpos : 0 <
      (DusartThetaTable66Chunk.appendMany first rest).cutoff)
    (hlogX : (10 : Real) < Real.log
      (DusartThetaTable66Chunk.appendMany first rest).cutoff)
    (hA_nonneg : 0 ≤ A)
    (hA : A / Real.log
      (DusartThetaTable66Chunk.appendMany first rest).cutoff ≤
      12167 / 500000)
    (thetaError : HasThetaLogFourthError A
      (DusartThetaTable66Chunk.appendMany first rest).cutoff) :
    ∀ y : Real, 0 < y →
      Chebyshev.theta y < (1000081 : Real) / 1000000 * y := by
  exact wangCrapis_theta_upper_1000081_of_finite_and_logFourthTail
    hXpos hlogX
    (hasDusartSymmetricThetaBoundsBelow_of_table66_chunks first rest)
    hA_nonneg hA thetaError

/-! Selected-cutoff form used by the split all-`k` assembly. -/
theorem wangCrapis_thetaBounds_of_selected_cutoff
    {A X : Real} (finite : HasDusartSymmetricThetaBoundsBelow X)
    (hXpos : 0 < X) (hlogX : (10 : Real) < Real.log X)
    (hA_nonneg : 0 ≤ A)
    (hA : A / Real.log X ≤ 12167 / 500000)
    (thetaError : HasThetaLogFourthErrorAbove A X) :
    HasDusartThetaBounds := by
  apply wangCrapis_thetaBounds_of_logFourthTail
    hXpos hlogX finite hA_nonneg hA
  intro x hx
  exact thetaError x hx

/-! A source-level decay adapter.  This is deliberately stated in terms of
the underlying r-power decay estimate rather than a prepackaged Dusart
theorem.  The decay-to-log-fourth conversion chooses an eventual cutoff;
the caller supplies the finite theta verification up to that same cutoff.
The numerical hypothesis is exactly the margin required by the published
theta assembly. -/
theorem wangCrapis_thetaBounds_of_rpowDecay
    {C c α X : Real}
    (hXpos : 0 < X)
    (hlogX : (500000 : Real) / 12167 < Real.log X)
    (hC : 0 ≤ C) (hc : 0 < c) (hα : 0 < α)
    (decay : HasThetaLogRpowDecay C c α X)
    (finite : ∀ Y : Real, X ≤ Y →
      HasDusartSymmetricThetaBoundsBelow Y) :
    HasDusartThetaBounds := by
  obtain ⟨Y, hXY, thetaError⟩ :=
    exists_hasThetaLogFourthError_of_logRpowDecay_of_pos_coefficient
      (C := C) (D := (1 : Real)) hC (by norm_num) hc hα decay
  have hYpos : 0 < Y := hXpos.trans hXY
  have hlogY : (10 : Real) < Real.log Y := by
    have hlog_mono : Real.log X ≤ Real.log Y :=
      Real.log_le_log hXpos hXY
    have hmargin : (10 : Real) < (500000 : Real) / 12167 := by
      norm_num
    linarith
  have hA : (1 : Real) / Real.log Y ≤ 12167 / 500000 := by
    have hlogY_pos : 0 < Real.log Y := Real.log_pos (by linarith)
    apply (div_le_iff₀ hlogY_pos).2
    nlinarith
  exact wangCrapis_thetaBounds_of_logFourthTail
    hYpos hlogY (finite Y hXY) (by norm_num) hA thetaError

/-! The same assembly specialized to the project's medium-PNT
adapter.  The only remaining input is the bounded endpoint verification;
the unbounded analytic tail is supplied by the proved source-level PNT
argument, not by a Dusart theorem imported as an assumption. -/
theorem wangCrapis_thetaBounds_of_mediumPNT
    (finite : ∀ Y : Real, (4e18 : Real) ≤ Y →
      HasDusartSymmetricThetaBoundsBelow Y) :
    HasDusartThetaBounds := by
  obtain ⟨Y, hY, h4Y, hlogY, thetaError⟩ :=
    exists_hasThetaLogFourthError_of_mediumPNT_at_large_cutoff
  have hYpos : 0 < Y := by linarith
  have hA : (648 / 1000 : Real) / Real.log Y ≤
      12167 / 500000 := by
    have hlogYpos : 0 < Real.log Y := by linarith
    apply (div_le_iff₀ hlogYpos).2
    nlinarith
  exact wangCrapis_thetaBounds_of_logFourthTail
    hYpos (by linarith) (finite Y h4Y) (by norm_num) hA thetaError

/-! One finite prefix is enough once the source-level tail has chosen its
cutoff.  This is the boundary consumed by a shared finite certificate package.
-/
theorem wangCrapis_thetaBounds_of_selected_mediumPNT_cutoff
    (selected : ∃ Y : Real, (4e18 : Real) ≤ Y ∧
      HasDusartSymmetricThetaBoundsBelow Y ∧
      HasThetaLogFourthError (648 / 1000 : Real) Y) :
    HasDusartThetaBounds := by
  obtain ⟨Y, h4Y, finite, thetaError⟩ := selected
  have hYpos : 0 < Y := by linarith
  have hlogY : (42 : Real) ≤ Real.log Y := by
    exact forty_two_lt_log_four_e18.le.trans
      (Real.log_le_log (by norm_num) h4Y)
  have hA : (648 / 1000 : Real) / Real.log Y ≤
      12167 / 500000 := by
    have hlogYpos : 0 < Real.log Y := by linarith
    apply (div_le_iff₀ hlogYpos).2
    nlinarith
  exact wangCrapis_thetaBounds_of_logFourthTail
    hYpos (by linarith) finite (by norm_num) hA thetaError

/-! The source-level decay route can also provide the theta provider directly.
The finite endpoint argument is the only bounded input: the arbitrary
coefficient delivered by the PNT is absorbed by raising the selected cutoff
to an explicit exponential threshold. -/
theorem wangCrapis_thetaBounds_of_mediumPNT_via_decay
    (finite : ∀ Y : Real, (4e18 : Real) ≤ Y →
      HasDusartSymmetricThetaBoundsBelow Y) :
    HasDusartThetaBounds := by
  obtain ⟨C, Y₀, hC, h4Y₀, thetaError₀⟩ :=
    exists_hasThetaLogFourthError_of_mediumPNT_via_decay
  let L : Real := max 100 (((C + 1) * 500000 / 12167) + 1)
  let Y : Real := max Y₀ (Real.exp L)
  have hY₀ : Y₀ ≤ Y := le_max_left _ _
  have hexpY : Real.exp L ≤ Y := le_max_right _ _
  have hYpos : 0 < Y := by
    exact (Real.exp_pos L).trans_le hexpY
  have h4Y : (4e18 : Real) ≤ Y := h4Y₀.trans hY₀
  have hlogY : (10 : Real) < Real.log Y := by
    have hL100 : (100 : Real) ≤ L := le_max_left _ _
    have hlog : L ≤ Real.log Y :=
      (Real.le_log_iff_exp_le hYpos).2 hexpY
    linarith
  have thetaError : HasThetaLogFourthError (C + 1) Y := by
    intro x hx
    exact thetaError₀ x (hY₀.trans hx)
  have hA0 : 0 ≤ C + 1 := by linarith
  have hA : (C + 1) / Real.log Y ≤ 12167 / 500000 := by
    have hlogYpos : 0 < Real.log Y := by linarith
    apply (div_le_iff₀ hlogYpos).2
    have hLcoef : ((C + 1) * 500000 / 12167) + 1 ≤ L :=
      le_max_right _ _
    have hLlog : L ≤ Real.log Y :=
      (Real.le_log_iff_exp_le hYpos).2 hexpY
    nlinarith
  exact wangCrapis_thetaBounds_of_logFourthTail
    hYpos hlogY (finite Y h4Y) hA0 hA thetaError

end

end PrimeFactorUnimodality
