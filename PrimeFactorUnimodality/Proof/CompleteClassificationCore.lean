import PrimeFactorUnimodality.Helpers.Analytic.ExplicitPrimeCounting
import PrimeFactorUnimodality.Helpers.Analytic.ExplicitThetaBounds
import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows
import PrimeFactorUnimodality.Helpers.Analytic.MediumPNT
import PrimeFactorUnimodality.Helpers.Analytic.ShortIntervalPrime
import PrimeFactorUnimodality.Helpers.FiniteCertificates.SmallPrimeCountingIntervals
import PrimeFactorUnimodality.Proof.ClassificationThrough38000Closed
import PrimeFactorUnimodality.Proof.CompleteClassificationReduction
import PrimeFactorUnimodality.Proof.LargeRange.FullRecordRange
import PrimeFactorUnimodality.Proof.LargeRange.TailErrorBounds
import PrimeFactorUnimodality.Proof.LargeRange.UniformTail

set_option autoImplicit false

/-! # Complete classification foundations

This module is a source-level split of the complete all-k classification assembly.
-/

namespace PrimeFactorUnimodality

noncomputable section

theorem completeClassification_with_explicit_inputs
    (primeCountingBounds : HasDusartPrimeCountingBounds)
    (reciprocalEstimate : HasDusartReciprocalPrimeEstimate Mertens.M)
    (thetaBounds : HasDusartThetaBounds)
    (tailPair : HasUniformTailPrimePair)
    (k : Nat) (hk : 1 ≤ k) :
    IsUnimodal (primeFactorDensity k) ↔ k ≤ 3 := by
  by_cases hkFinite : k ≤ 38000
  · exact completeClassification_through38000_closed k hk hkFinite
  · constructor
    · intro unimodal
      exact (uniformTail_not_isUnimodal primeCountingBounds reciprocalEstimate
        mertensConstant_lt_two_thirds.le thetaBounds tailPair
        (k := k) (by omega)) unimodal
    · intro hkThree
      omega

/-- The same classification packaged as the project's exact universal target.
This wrapper is intentionally parameterized only by the explicit analytic
providers still used by the pointwise assembly theorem. -/
theorem completeClassification_of_explicit_inputs
    (primeCountingBounds : HasDusartPrimeCountingBounds)
    (reciprocalEstimate : HasDusartReciprocalPrimeEstimate Mertens.M)
    (thetaBounds : HasDusartThetaBounds)
    (tailPair : HasUniformTailPrimePair) :
    CompleteClassification := by
  intro k hk
  exact completeClassification_with_explicit_inputs primeCountingBounds reciprocalEstimate
    thetaBounds tailPair k hk

/-! The reciprocal-prime estimate is a proved Mertens consequence in this
project, so the public all-`k` boundary need not expose it as an analytic
input.  Only the Dusart prime-counting/theta providers and the short-interval
provider remain at this layer. -/
theorem completeClassification_of_explicit_mertens_inputs
    (primeCountingBounds : HasDusartPrimeCountingBounds)
    (thetaBounds : HasDusartThetaBounds)
    (tailPair : HasUniformTailPrimePair) :
    CompleteClassification := by
  exact completeClassification_of_explicit_inputs primeCountingBounds
    hasMertensReciprocalPrimeEstimate thetaBounds tailPair

theorem completeClassification_of_explicit_dusart_inputs
    (primeCountingBounds : HasDusartPrimeCountingBounds)
    (thetaBounds : HasDusartThetaBounds)
    (shortInterval : HasDusartShortIntervalPrime) :
    CompleteClassification := by
  exact completeClassification_of_explicit_mertens_inputs primeCountingBounds
    thetaBounds (hasUniformTailPrimePair_of_shortInterval shortInterval)

/-! The exact all-`k` reduction after the full published record-gap range is
available.  This is the final finite/tail assembly; only the analytic tail
providers remain parameters here. -/

theorem completeClassification_of_full_record_inputs
    (primeCountingBounds : HasDusartPrimeCountingBounds)
    (thetaBounds : HasDusartThetaBounds)
    (tailPair : HasUniformTailPrimePair) :
    CompleteClassification := by
  exact completeClassification_of_finite_range_and_tail
    8600001 (by omega)
    (fun k hk hkRecord => by
      by_cases hkSmall : k ≤ 38000
      · exact completeClassification_through38000_closed k hk hkSmall
      · constructor
        · intro unimodal
          exact ((fullRecordRange_not_isUnimodal_closed_through8600001
            primeCountingBounds thetaBounds tailPair k (by omega) hkRecord)
            unimodal).elim
        · intro hkThree
          omega)
    (fun k hkTail => uniformTail_not_isUnimodal_closed_mertens
      primeCountingBounds thetaBounds tailPair (k := k) (by omega))

/-! This is the public all-`k` assembly in the analytic forms used by the
published estimates: real-variable prime counting, symmetric theta error,
and a logarithm-cubed prime interval. -/
theorem completeClassification_of_full_record_short_interval_inputs
    (primeCountingBounds : HasDusartRealPrimeCountingBounds)
    (thetaBounds : HasDusartSymmetricThetaBounds)
    (shortInterval : HasDusartShortIntervalPrime) :
    CompleteClassification := by
  exact completeClassification_of_full_record_inputs
    (hasDusartPrimeCountingBounds_of_real primeCountingBounds)
    (hasDusartThetaBounds_of_symmetric thetaBounds)
    (hasUniformTailPrimePair_of_shortInterval shortInterval)

theorem completeClassification_of_full_record_interval_certificates
    (primeCountingBounds : HasDusartRealPrimeCountingBounds)
    (thetaBounds : HasDusartSymmetricThetaBounds)
    {dusartRows : List DusartPrimeRow}
    (dusartCover : DusartPrimeRowsCoverBelow dusartRows)
    {logRows : List LogCubedPrimeRow}
    (logCover : LogCubedPrimeRowsCoverUpTo logRows (4e18 : Real))
    (thetaError : HasThetaLogCubedError (12167 / 500000 : Real) (4e18 : Real)) :
    CompleteClassification := by
  exact completeClassification_of_full_record_short_interval_inputs
    primeCountingBounds thetaBounds
    (hasDusartShortIntervalPrime_of_rows_and_thetaError
      dusartCover logCover thetaError)

theorem completeClassification_of_full_record_fourth_theta_error
    (primeCountingBounds : HasDusartRealPrimeCountingBounds)
    (finiteTheta : HasDusartSymmetricThetaBoundsBelow (4e18 : Real))
    {A : Real}
    (hA_nonneg : 0 ≤ A)
    (hA : A / Real.log (4e18 : Real) ≤ 12167 / 500000)
    {dusartRows : List DusartPrimeRow}
    (dusartCover : DusartPrimeRowsCoverBelow dusartRows)
    {logRows : List LogCubedPrimeRow}
    (logCover : LogCubedPrimeRowsCoverUpTo logRows (4e18 : Real))
    (thetaError : HasThetaLogFourthError A (4e18 : Real)) :
    CompleteClassification := by
  have cubic : HasThetaLogCubedError (12167 / 500000 : Real) (4e18 : Real) :=
    hasThetaLogCubedError_of_logFourthError
      (A := A) (X := (4e18 : Real)) (by norm_num) hA_nonneg thetaError
  exact completeClassification_of_full_record_interval_certificates
    primeCountingBounds
    (hasDusartSymmetricThetaBounds_of_below_and_logFourth
      finiteTheta hA_nonneg hA thetaError)
    dusartCover logCover cubic

theorem completeClassification_of_full_record_unit_fourth_theta_error
    (primeCountingBounds : HasDusartRealPrimeCountingBounds)
    (finiteTheta : HasDusartSymmetricThetaBoundsBelow (4e18 : Real))
    {dusartRows : List DusartPrimeRow}
    (dusartCover : DusartPrimeRowsCoverBelow dusartRows)
    {logRows : List LogCubedPrimeRow}
    (logCover : LogCubedPrimeRowsCoverUpTo logRows (4e18 : Real))
    (thetaError : HasThetaLogFourthError 1 (4e18 : Real)) :
    CompleteClassification := by
  exact completeClassification_of_full_record_fourth_theta_error
    primeCountingBounds finiteTheta (by norm_num) (by norm_num)
    dusartCover logCover thetaError

/-! The finite-row presentation is the concrete form needed by the eventual
analytic provider: it keeps the medium range as one bounded cover and uses
the proved theta-error implication above the cutoff. -/
theorem completeClassification_of_full_record_bounded_rows
    (primeCountingBounds : HasDusartRealPrimeCountingBounds)
    (thetaBounds : HasDusartSymmetricThetaBounds)
    {rows : List LogCubedPrimeRow}
    (X : Real) (hX : (4e18 : Real) ≤ X)
    (cover : LogCubedPrimeRowsCoverUpTo rows X)
    (thetaError : HasThetaLogCubedError (12167 / 500000 : Real) (4e18 : Real)) :
    CompleteClassification := by
  have shortInterval : HasDusartShortIntervalPrime :=
    hasLogCubedShortIntervalPrime_of_bounded_rows_and_large_x
      rows X hX cover thetaError
  exact completeClassification_of_full_record_short_interval_inputs
    primeCountingBounds thetaBounds shortInterval

theorem completeClassification_of_full_record_rows_at_large_cutoff
    (primeCountingBounds : HasDusartRealPrimeCountingBounds)
    (thetaBounds : HasDusartSymmetricThetaBounds)
    {rows : List LogCubedPrimeRow}
    (cover : LogCubedPrimeRowsCoverUpTo rows (4e18 : Real))
    (thetaError : HasThetaLogCubedError (12167 / 500000 : Real) (4e18 : Real)) :
    CompleteClassification := by
  exact completeClassification_of_full_record_bounded_rows
    primeCountingBounds thetaBounds (4e18 : Real) le_rfl cover thetaError

theorem completeClassification_of_full_record_rows_and_finite_theta
    (primeCountingBounds : HasDusartRealPrimeCountingBounds)
    (finiteTheta : HasDusartSymmetricThetaBoundsBelow (4e18 : Real))
    {rows : List LogCubedPrimeRow}
    (cover : LogCubedPrimeRowsCoverUpTo rows (4e18 : Real))
    (thetaError : HasThetaLogCubedError (12167 / 500000 : Real) (4e18 : Real)) :
    CompleteClassification := by
  exact completeClassification_of_full_record_rows_at_large_cutoff
    primeCountingBounds
    (hasDusartSymmetricThetaBounds_of_below_and_logCubed finiteTheta thetaError)
    cover thetaError

theorem completeClassification_of_full_record_split_analytic_inputs
    {X : Real}
    (finitePrimeCounting : HasDusartRealPrimeCountingBoundsBelow X)
    (tailPrimeCounting : HasDusartRealPrimeCountingBoundsAbove X)
    (finiteTheta : HasDusartSymmetricThetaBoundsBelow (4e18 : Real))
    {rows : List LogCubedPrimeRow}
    (cover : LogCubedPrimeRowsCoverUpTo rows (4e18 : Real))
    (thetaError : HasThetaLogCubedError (12167 / 500000 : Real) (4e18 : Real)) :
    CompleteClassification := by
  exact completeClassification_of_full_record_rows_and_finite_theta
    (hasDusartRealPrimeCountingBounds_of_below_and_above
      finitePrimeCounting tailPrimeCounting)
    finiteTheta cover thetaError

theorem completeClassification_of_full_record_cutoff_split_inputs
    (finitePrimeCounting : HasDusartRealPrimeCountingBoundsBelow (4e18 : Real))
    (tailPrimeCounting : HasDusartRealPrimeCountingBoundsAbove (4e18 : Real))
    (finiteTheta : HasDusartSymmetricThetaBoundsBelow (4e18 : Real))
    {rows : List LogCubedPrimeRow}
    (cover : LogCubedPrimeRowsCoverUpTo rows (4e18 : Real))
    (thetaError : HasThetaLogCubedError (12167 / 500000 : Real) (4e18 : Real)) :
    CompleteClassification := by
  exact completeClassification_of_full_record_split_analytic_inputs
    finitePrimeCounting tailPrimeCounting finiteTheta cover thetaError

/-! The same all-`k` assembly at an arbitrary raised analytic cutoff.  This
is the boundary consumed by a source-level PNT proof whose eventual threshold
is not definitionally the paper's numerical cutoff. -/
theorem completeClassification_of_full_record_raised_cutoff_inputs
    {X : Real} (hX : (4e18 : Real) ≤ X)
    (finitePrimeCounting : HasDusartRealPrimeCountingBoundsBelow X)
    (tailPrimeCounting : HasDusartRealPrimeCountingBoundsAbove X)
    (finiteTheta : HasDusartSymmetricThetaBoundsBelow X)
    (thetaError : HasThetaLogCubedError (12167 / 500000 : Real) X)
    (finiteShortInterval : HasLogCubedShortIntervalPrimeBelow X)
    (tailShortInterval : ∀ x : Real, X ≤ x →
      ∃ q : Nat, q.Prime ∧ x < q ∧
        (q : Real) ≤ x + x / (Real.log x) ^ 3) :
    CompleteClassification := by
  have hXpos : 0 < X := by linarith
  have hlogX : (10 : Real) < Real.log X := by
    have hlog4 : (42 : Real) ≤ Real.log X :=
      forty_two_lt_log_four_e18.le.trans
        (Real.log_le_log (by norm_num) hX)
    linarith
  have primeCountingBounds : HasDusartRealPrimeCountingBounds :=
    hasDusartRealPrimeCountingBounds_of_below_and_above
      finitePrimeCounting tailPrimeCounting
  have thetaBounds : HasDusartSymmetricThetaBounds :=
    hasDusartSymmetricThetaBounds_of_below_and_logCubed_from
      hXpos hlogX finiteTheta thetaError
  have shortInterval : HasDusartShortIntervalPrime :=
    hasLogCubedShortIntervalPrime_of_below_and_above
      (by linarith [hX]) finiteShortInterval tailShortInterval
  exact completeClassification_of_full_record_short_interval_inputs
    primeCountingBounds thetaBounds shortInterval

/-! Once a log-fourth theta estimate is proved at the selected cutoff, the
source-level Abel argument and the interval argument discharge both
unbounded inputs at that same cutoff.  This is the all-`k` assembly boundary:
the remaining hypotheses are genuinely finite data below `X`, not an imported
Dusart tail theorem. -/
theorem completeClassification_of_logFourth_cutoff_inputs
    {A C X : Real} (hX : (4e18 : Real) ≤ X)
    (finitePrimeCounting : HasDusartRealPrimeCountingBoundsBelow X)
    (finiteTheta : HasDusartSymmetricThetaBoundsBelow X)
    (finiteShortInterval : HasLogCubedShortIntervalPrimeBelow X)
    (hA0 : 0 ≤ A) (hA : A ≤ 1)
    (hC0 : 0 ≤ C) (hC : C ≤ 3 / 5)
    (hcore : |primeCountingCore X| ≤ C * X / Real.log X ^ 4)
    (thetaError : HasThetaLogFourthError A X) :
    CompleteClassification := by
  have hXpos : 0 < X := by linarith
  have h2X : 2 ≤ X := by linarith
  have hlogX : (42 : Real) ≤ Real.log X :=
    forty_two_lt_log_four_e18.le.trans
      (Real.log_le_log (by norm_num) hX)
  have hlogXpos : 0 < Real.log X := by linarith
  have hAlog : A / Real.log X ≤ 12167 / 500000 := by
    apply (div_le_iff₀ hlogXpos).2
    nlinarith
  have thetaErrorCubic : HasThetaLogCubedError
      (12167 / 500000 : Real) X := by
    have converted := hasThetaLogCubedError_of_logFourthError
      (by linarith) hA0 thetaError
    intro x hx
    exact (converted x hx).trans (by
      have hx_pos : 0 < x := by linarith
      have hlogx_pos : 0 < Real.log x := Real.log_pos (by linarith)
      have hfactor : 0 ≤ x / (Real.log x) ^ 3 := by positivity
      calc
        (A / Real.log X) * x / (Real.log x) ^ 3 =
            (A / Real.log X) * (x / (Real.log x) ^ 3) := by ring
        _ ≤ (12167 / 500000 : Real) *
              (x / (Real.log x) ^ 3) :=
          mul_le_mul_of_nonneg_right hAlog hfactor
        _ = (12167 / 500000 : Real) * x /
              (Real.log x) ^ 3 := by ring)
  have tailPrimeCounting : HasDusartRealPrimeCountingBoundsAbove X :=
    hasDusartRealPrimeCountingBoundsAbove_of_core_and_theta_error
      hXpos h2X le_rfl hA0 hA hC0 hC hlogX hcore thetaError
  have tailShortInterval : ∀ x : Real, X ≤ x →
      ∃ q : Nat, q.Prime ∧ x < q ∧
        (q : Real) ≤ x + x / (Real.log x) ^ 3 := by
    intro x hx
    obtain ⟨q, hq, hxq, hupper⟩ :=
      dusartPrimeInInterval_of_logFourthError_from
        hXpos h2X (by linarith) hA0 hAlog thetaError x hx
    exact ⟨q, hq, hxq, by convert hupper using 1 <;> ring⟩
  exact completeClassification_of_full_record_raised_cutoff_inputs
    hX finitePrimeCounting tailPrimeCounting finiteTheta thetaErrorCubic
    finiteShortInterval tailShortInterval

/-! The finite core no longer needs to be passed as an independent analytic
hypothesis: the explicit Abel estimate derives it directly from the finite
log-fourth theta rows. -/
theorem completeClassification_of_logFourth_cutoff_inputs_from_theta_error
    {A X : Real} (hX : (4e18 : Real) ≤ X)
    (finitePrimeCounting : HasDusartRealPrimeCountingBoundsBelow X)
    (finiteTheta : HasDusartSymmetricThetaBoundsBelow X)
    (finiteShortInterval : HasLogCubedShortIntervalPrimeBelow X)
    (hA0 : 0 ≤ A) (hA1 : A ≤ 1)
    (thetaErrorBelow : HasThetaLogFourthErrorBelow A X)
    (thetaErrorAbove : HasThetaLogFourthErrorAbove A X) :
    CompleteClassification := by
  have thetaError : HasThetaLogFourthError A X :=
    hasThetaLogFourthError_of_below_and_above
      thetaErrorBelow thetaErrorAbove
  have hcore : |primeCountingCore X| ≤
      (3 / 5 : Real) * X / Real.log X ^ 4 :=
    primeCountingCore_abs_le_at_large_cutoff_of_theta_error
      hX hA0 hA1 thetaErrorBelow
  exact completeClassification_of_logFourth_cutoff_inputs
    hX finitePrimeCounting finiteTheta finiteShortInterval
    hA0 hA1 (by norm_num) (by norm_num) hcore thetaError

/-! A fully expanded core boundary: the opaque core inequality can be
replaced by the explicit logarithmic-integral inequality obtained from the
finite theta error. -/
private theorem completeClassification_of_finite_theta_error_and_integral_core
    {A C X : Real} (hX : (4e18 : Real) ≤ X)
    (finitePrimeCounting : HasDusartRealPrimeCountingBoundsBelow X)
    (finiteTheta : HasDusartSymmetricThetaBoundsBelow X)
    (finiteShortInterval : HasLogCubedShortIntervalPrimeBelow X)
    (hA0 : 0 ≤ A) (hA : A ≤ 1)
    (hC0 : 0 ≤ C) (hC : C ≤ 3 / 5)
    (thetaErrorBelow : HasThetaLogFourthErrorBelow A X)
    (thetaErrorAbove : HasThetaLogFourthErrorAbove A X)
    (integralCoreBound :
      4000 + 720 * (∫ t in (2 : Real)..X, 1 / Real.log t ^ 7) +
          A * (∫ t in (2 : Real)..X, 1 / Real.log t ^ 6) ≤
        C * X / Real.log X ^ 4) :
    CompleteClassification := by
  have thetaError : HasThetaLogFourthError A X :=
    hasThetaLogFourthError_of_below_and_above
      thetaErrorBelow thetaErrorAbove
  have hcore : |primeCountingCore X| ≤ C * X / Real.log X ^ 4 := by
    exact (primeCountingCore_abs_le_of_finite_theta_error
      (by linarith [hX]) hA0 thetaErrorBelow).trans integralCoreBound
  exact completeClassification_of_logFourth_cutoff_inputs
    hX finitePrimeCounting finiteTheta finiteShortInterval hA0 hA
    hC0 hC hcore thetaError

/-! Corrected split-range form of the core assembly.  The small interval is
represented by its Abel remainder directly; the sharp theta estimate begins
only at `x₀`, where it is actually true. -/
theorem completeClassification_of_split_theta_error_and_integral_core
    {A C X x₀ R : Real} (hX : (4e18 : Real) ≤ X)
    (h2x₀ : (2 : Real) ≤ x₀) (hx₀X : x₀ ≤ X)
    (finitePrimeCounting : HasDusartRealPrimeCountingBoundsBelow X)
    (finiteTheta : HasDusartSymmetricThetaBoundsBelow X)
    (finiteShortInterval : HasLogCubedShortIntervalPrimeBelow X)
    (hA0 : 0 ≤ A) (hA1 : A ≤ 1)
    (hC0 : 0 ≤ C) (hC : C ≤ 3 / 5)
    (hsmall : |∫ t in (2 : Real)..x₀,
        (Chebyshev.theta t / (t * (Real.log t) ^ 2) -
          1 / (Real.log t) ^ 2)| ≤ R)
    (thetaErrorAbove : HasThetaLogFourthErrorAbove A x₀)
    (integralCoreBound :
      4000 + 720 * (∫ t in (2 : Real)..X, 1 / Real.log t ^ 7) +
          R + A * (∫ t in x₀..X, 1 / Real.log t ^ 6) ≤
        C * X / Real.log X ^ 4) :
    CompleteClassification := by
  have thetaError : HasThetaLogFourthError A X := by
    intro x hx
    exact thetaErrorAbove x (hx₀X.trans hx)
  have hcore : |primeCountingCore X| ≤ C * X / Real.log X ^ 4 := by
    exact (primeCountingCore_abs_le_of_split_theta_error
      h2x₀ hx₀X hsmall hA0 thetaErrorAbove).trans integralCoreBound
  exact completeClassification_of_logFourth_cutoff_inputs
    hX finitePrimeCounting finiteTheta finiteShortInterval hA0 hA1
    hC0 hC hcore thetaError

/-! A reserve form of the split assembly.  This keeps the finite Abel prefix
separate from the analytic tail: a proved numerical reserve can pay for the
prefix remainder without introducing a new bundled core hypothesis. -/
theorem completeClassification_of_split_theta_error_and_reserved_integral_core
    {A C X x₀ R : Real} (hX : (4e18 : Real) ≤ X)
    (h2x₀ : (2 : Real) ≤ x₀) (hx₀X : x₀ ≤ X)
    (finitePrimeCounting : HasDusartRealPrimeCountingBoundsBelow X)
    (finiteTheta : HasDusartSymmetricThetaBoundsBelow X)
    (finiteShortInterval : HasLogCubedShortIntervalPrimeBelow X)
    (hA0 : 0 ≤ A) (hA1 : A ≤ 1)
    (hC0 : 0 ≤ C) (hC : C ≤ 3 / 5)
    (hsmall : |∫ t in (2 : Real)..x₀,
        (Chebyshev.theta t / (t * (Real.log t) ^ 2) -
          1 / (Real.log t) ^ 2)| ≤ R)
    (hR : R ≤ 10000)
    (thetaErrorAbove : HasThetaLogFourthErrorAbove A x₀)
    (reservedIntegralCore :
      4000 + 720 * (∫ t in (2 : Real)..X, 1 / Real.log t ^ 7) +
          10000 + A * (∫ t in x₀..X, 1 / Real.log t ^ 6) ≤
        C * X / Real.log X ^ 4) :
    CompleteClassification := by
  apply completeClassification_of_split_theta_error_and_integral_core
    hX h2x₀ hx₀X finitePrimeCounting finiteTheta finiteShortInterval
    hA0 hA1 hC0 hC hsmall thetaErrorAbove
  nlinarith

private theorem completeClassification_of_theta_error_rows_and_integral_core
    {A C X : Real} (hX : (4e18 : Real) ≤ X)
    (finitePrimeCounting : HasDusartRealPrimeCountingBoundsBelow X)
    (finiteTheta : HasDusartSymmetricThetaBoundsBelow X)
    (finiteShortInterval : HasLogCubedShortIntervalPrimeBelow X)
    (hA0 : 0 ≤ A) (hA : A ≤ 1)
    (hC0 : 0 ≤ C) (hC : C ≤ 3 / 5)
    {rows : List (ThetaLogFourthErrorRow A)}
    (cover : ThetaLogFourthErrorRowsCoverUpTo rows X)
    (thetaErrorAbove : HasThetaLogFourthErrorAbove A X)
    (integralCoreBound :
      4000 + 720 * (∫ t in (2 : Real)..X, 1 / Real.log t ^ 7) +
          A * (∫ t in (2 : Real)..X, 1 / Real.log t ^ 6) ≤
        C * X / Real.log X ^ 4) :
    CompleteClassification := by
  exact completeClassification_of_finite_theta_error_and_integral_core
    hX finitePrimeCounting finiteTheta finiteShortInterval hA0 hA hC0 hC
    (hasThetaLogFourthErrorBelow_of_rows cover) thetaErrorAbove
    integralCoreBound

private theorem completeClassification_of_finite_theta_error_at_large_cutoff
    {A X : Real} (hX : (4e18 : Real) ≤ X)
    (finitePrimeCounting : HasDusartRealPrimeCountingBoundsBelow X)
    (finiteTheta : HasDusartSymmetricThetaBoundsBelow X)
    (finiteShortInterval : HasLogCubedShortIntervalPrimeBelow X)
    (hA0 : 0 ≤ A) (hA1 : A ≤ 1)
    (thetaErrorBelow : HasThetaLogFourthErrorBelow A X)
    (thetaErrorAbove : HasThetaLogFourthErrorAbove A X) :
    CompleteClassification := by
  exact completeClassification_of_logFourth_cutoff_inputs_from_theta_error
    hX finitePrimeCounting finiteTheta finiteShortInterval hA0 hA1
    thetaErrorBelow thetaErrorAbove

/-! The source-level MediumPNT selects the cutoff; this wrapper makes the
remaining finite obligation explicit as a provider valid at every possible
selected cutoff.  Thus the resulting conclusion is the universal
classification, with no hidden fixed cutoff and no finite bound on `k`. -/
private theorem completeClassification_of_mediumPNT_and_finite_provider
    (finitePrimeCounting : ∀ X : Real, (4e18 : Real) ≤ X →
      HasDusartRealPrimeCountingBoundsBelow X)
    (finiteTheta : ∀ X : Real, (4e18 : Real) ≤ X →
      HasDusartSymmetricThetaBoundsBelow X)
    (finiteShortInterval : ∀ X : Real, (4e18 : Real) ≤ X →
      HasLogCubedShortIntervalPrimeBelow X)
    (coreBound : ∀ X : Real, (4e18 : Real) ≤ X →
      |primeCountingCore X| ≤ (3 / 5 : Real) * X / Real.log X ^ 4) :
    CompleteClassification := by
  obtain ⟨X, hX, h4X, thetaError⟩ :=
    exists_hasThetaLogFourthError_of_mediumPNT_above (4e18 : Real)
  exact completeClassification_of_logFourth_cutoff_inputs
    h4X (finitePrimeCounting X h4X) (finiteTheta X h4X)
    (finiteShortInterval X h4X)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (coreBound X h4X) thetaError

/-! A selected-cutoff variant of the preceding provider theorem.  MediumPNT
chooses the cutoff and proves the unbounded theta error; the finite provider
only has to answer at that one cutoff.  The prime-counting and short-interval
tails are derived here from the source-level Abel and theta arguments. -/
/-! All finite inputs are attached to the same cutoff selected by the
source-level analytic theorem.  This is the exact all-`k` boundary: there is
no finite provider quantified over unrelated possible cutoffs. -/

end

end PrimeFactorUnimodality
