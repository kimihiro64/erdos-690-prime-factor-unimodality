import PrimeFactorUnimodality.Proof.ClassificationThrough38000Closed
import PrimeFactorUnimodality.Proof.CompleteClassificationReduction
import PrimeFactorUnimodality.Proof.LargeRange.FullRecordRange
import PrimeFactorUnimodality.Proof.LargeRange.UniformTail
import PrimeFactorUnimodality.Proof.LargeRange.TailErrorBounds
import PrimeFactorUnimodality.Helpers.Analytic.ExplicitPrimeCounting
import PrimeFactorUnimodality.Helpers.Analytic.ExplicitThetaBounds
import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows
import PrimeFactorUnimodality.Helpers.Analytic.MediumPNT
import PrimeFactorUnimodality.Helpers.Analytic.ShortIntervalPrime
import PrimeFactorUnimodality.Helpers.FiniteCertificates.SmallPrimeCountingIntervals

set_option autoImplicit false

/-! # Complete classification from the explicit analytic inputs -/

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
    7430000 (by omega)
    (fun k hk hkRecord => by
      by_cases hkSmall : k ≤ 38000
      · exact completeClassification_through38000_closed k hk hkSmall
      · constructor
        · intro unimodal
          exact ((fullRecordRange_not_isUnimodal_closed k (by omega) hkRecord)
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
structure MediumPNTSelectedFiniteInputs (A X : Real) : Prop where
  cutoff : Real
  lower : X ≤ cutoff
  large : (4e18 : Real) ≤ cutoff
  thetaError : HasThetaLogFourthError A cutoff
  primeCounting : HasDusartRealPrimeCountingBoundsBelow cutoff
  theta : HasDusartSymmetricThetaBoundsBelow cutoff
  shortInterval : HasLogCubedShortIntervalPrimeBelow cutoff

theorem mediumPNTSelectedFiniteInputs_of_cutoff
    {A X Y : Real}
    (hXY : X ≤ Y) (h4Y : (4e18 : Real) ≤ Y)
    (thetaError : HasThetaLogFourthError A Y)
    (finitePrimeCounting : HasDusartRealPrimeCountingBoundsBelow Y)
    (finiteTheta : HasDusartSymmetricThetaBoundsBelow Y)
    (finiteShortInterval : HasLogCubedShortIntervalPrimeBelow Y) :
    MediumPNTSelectedFiniteInputs A X := by
  exact {
    cutoff := Y
    lower := hXY
    large := h4Y
    thetaError := thetaError
    primeCounting := finitePrimeCounting
    theta := finiteTheta
    shortInterval := finiteShortInterval }

theorem mediumPNTSelectedFiniteInputs_of_lists
    {A X Y : Real}
    (hXY : X ≤ Y) (h4Y : (4e18 : Real) ≤ Y)
    {primeRows : List DusartPrimeCountingEndpointRow}
    (primeCover : DusartPrimeCountingEndpointRowsCoverFrom599 primeRows Y)
    {thetaRows : List DusartThetaEndpointRow}
    (thetaCover : DusartThetaEndpointRowsCoverUpTo thetaRows Y)
    {logRows : List LogCubedPrimeRow}
    (logCover : LogCubedPrimeRowsCoverUpTo logRows Y)
    (thetaError : HasThetaLogFourthError A Y) :
    MediumPNTSelectedFiniteInputs A X := by
  have finitePrimeCounting :
      HasDusartRealPrimeCountingBoundsBelow Y :=
    hasDusartRealPrimeCountingBoundsBelow_of_endpoint_rows
      primeCover dusartSmallUpperIntervalRows_provide
  have finiteTheta : HasDusartSymmetricThetaBoundsBelow Y :=
    hasDusartSymmetricThetaBoundsBelow_of_endpoint_rows thetaCover
  have finiteShortInterval : HasLogCubedShortIntervalPrimeBelow Y :=
    hasLogCubedShortIntervalPrimeBelow_of_indexed_rows
      (logCubedPrimeIndexedCover_of_list logCover)
  exact mediumPNTSelectedFiniteInputs_of_cutoff hXY h4Y thetaError
    finitePrimeCounting finiteTheta finiteShortInterval

theorem completeClassification_of_mediumPNT_and_selected_finite_inputs
    {A C X : Real} (hX : (4e18 : Real) ≤ X)
    (hA0 : 0 ≤ A) (hA1 : A ≤ 1)
    (hC0 : 0 ≤ C) (hC : C ≤ 3 / 5)
    (hcore : |primeCountingCore X| ≤ C * X / Real.log X ^ 4)
    (selectedInputs : MediumPNTSelectedFiniteInputs A X) :
    CompleteClassification := by
  let Y := selectedInputs.cutoff
  have hXY : X ≤ Y := selectedInputs.lower
  have h4Y : (4e18 : Real) ≤ Y := selectedInputs.large
  have thetaError := selectedInputs.thetaError
  have finitePrimeCounting := selectedInputs.primeCounting
  have finiteTheta := selectedInputs.theta
  have finiteShortInterval := selectedInputs.shortInterval
  have hXpos : 0 < X := by linarith
  have hX1 : 1 < X := by
    have hlogX : (42 : Real) ≤ Real.log X :=
      forty_two_lt_log_four_e18.le.trans
        (Real.log_le_log (by norm_num) hX)
    exact (Real.log_pos_iff hXpos.le).mp (by linarith)
  have hlogX : (42 : Real) ≤ Real.log X :=
    forty_two_lt_log_four_e18.le.trans
      (Real.log_le_log (by norm_num) hX)
  have hcoreY : |primeCountingCore X| ≤ C * Y / Real.log Y ^ 4 :=
    primeCountingCore_scale_le hX1 hXY (by linarith [hlogX]) hC0 hcore
  have hYpos : 0 < Y := lt_of_lt_of_le hXpos hXY
  have hlogY : (42 : Real) ≤ Real.log Y :=
    hlogX.trans (Real.log_le_log hXpos hXY)
  have tailPrimeCounting : HasDusartRealPrimeCountingBoundsAbove Y :=
    hasDusartRealPrimeCountingBoundsAbove_of_core_and_theta_error
      hYpos (by linarith [hlogY]) le_rfl
      hA0 hA1 hC0 hC hlogY hcoreY thetaError
  have hAlog : A / Real.log Y ≤
      (12167 / 500000 : Real) := by
    have hlogYpos : 0 < Real.log Y := by linarith
    apply (div_le_iff₀ hlogYpos).2
    nlinarith [hlogY]
  have thetaErrorCubic : HasThetaLogCubedError
      (12167 / 500000 : Real) Y := by
    have hconverted := hasThetaLogCubedError_of_logFourthError
      (A := A) (X := Y)
      (by linarith [hlogY]) hA0 thetaError
    intro x hx
    exact (hconverted x hx).trans (by
      have hx_pos : 0 < x := by linarith
      have hlogx_pos : 0 < Real.log x := Real.log_pos (by linarith)
      have hfactor : 0 ≤ x / (Real.log x) ^ 3 := by positivity
      calc
        (A / Real.log Y) * x /
              (Real.log x) ^ 3 =
            (A / Real.log Y) *
              (x / (Real.log x) ^ 3) := by ring
        _ ≤ (12167 / 500000 : Real) *
              (x / (Real.log x) ^ 3) :=
          mul_le_mul_of_nonneg_right hAlog hfactor
        _ = (12167 / 500000 : Real) * x /
              (Real.log x) ^ 3 := by ring)
  have tailShortInterval : ∀ x : Real, Y ≤ x →
      ∃ q : Nat, q.Prime ∧ x < q ∧
        (q : Real) ≤ x + x / (Real.log x) ^ 3 := by
    intro x hx
    obtain ⟨q, hq, hxq, hupper⟩ :=
      dusartPrimeInInterval_of_logFourthError_from
        hYpos (by linarith [hlogY]) (by linarith [hlogY])
        hA0 hAlog thetaError x hx
    exact ⟨q, hq, hxq, by convert hupper using 1 <;> ring⟩
  exact completeClassification_of_full_record_raised_cutoff_inputs
    h4Y finitePrimeCounting tailPrimeCounting finiteTheta thetaErrorCubic
    finiteShortInterval tailShortInterval

/-! Fully corrected selected-cutoff boundary.  The finite provider supplies
the Abel remainder over `[2,Y]`; MediumPNT supplies the sharp theta tail from
`Y` onward. -/
structure MediumPNTSelectedSplitInputs (X C : Real) : Prop where
  cutoff : Real
  lower : X ≤ cutoff
  large : (4e18 : Real) ≤ cutoff
  thetaError : HasThetaLogFourthErrorAbove (648 / 1000 : Real) cutoff
  primeCounting : HasDusartRealPrimeCountingBoundsBelow cutoff
  theta : HasDusartSymmetricThetaBoundsBelow cutoff
  shortInterval : HasLogCubedShortIntervalPrimeBelow cutoff
  remainder : ∃ R : Real,
    |∫ t in (2 : Real)..cutoff,
        (Chebyshev.theta t / (t * (Real.log t) ^ 2) -
          1 / (Real.log t) ^ 2)| ≤ R ∧
      4000 + 720 * (∫ t in (2 : Real)..cutoff, 1 / Real.log t ^ 7) + R ≤
        C * cutoff / Real.log cutoff ^ 4

theorem mediumPNTSelectedSplitInputs_of_cutoff
    {X C Y R : Real}
    (hXY : X ≤ Y) (h4Y : (4e18 : Real) ≤ Y)
    (thetaError : HasThetaLogFourthErrorAbove (648 / 1000 : Real) Y)
    (finitePrimeCounting : HasDusartRealPrimeCountingBoundsBelow Y)
    (finiteTheta : HasDusartSymmetricThetaBoundsBelow Y)
    (finiteShortInterval : HasLogCubedShortIntervalPrimeBelow Y)
    (hsmall :
      |∫ t in (2 : Real)..Y,
          (Chebyshev.theta t / (t * (Real.log t) ^ 2) -
            1 / (Real.log t) ^ 2)| ≤ R)
    (hcore :
      4000 + 720 * (∫ t in (2 : Real)..Y, 1 / Real.log t ^ 7) + R ≤
        C * Y / Real.log Y ^ 4) :
    MediumPNTSelectedSplitInputs X C := by
  exact {
    cutoff := Y
    lower := hXY
    large := h4Y
    thetaError := thetaError
    primeCounting := finitePrimeCounting
    theta := finiteTheta
    shortInterval := finiteShortInterval
    remainder := ⟨R, hsmall, hcore⟩ }

theorem completeClassification_of_mediumPNT_and_selected_split_inputs
    {X C : Real} (hX : (4e18 : Real) ≤ X)
    (hC0 : 0 ≤ C) (hC : C ≤ 3 / 5)
    (selectedInputs : MediumPNTSelectedSplitInputs X C) :
    CompleteClassification := by
  let Y := selectedInputs.cutoff
  have hXY : X ≤ Y := selectedInputs.lower
  have h4Y : (4e18 : Real) ≤ Y := selectedInputs.large
  have thetaError := selectedInputs.thetaError
  have finitePrimeCounting := selectedInputs.primeCounting
  have finiteTheta := selectedInputs.theta
  have finiteShortInterval := selectedInputs.shortInterval
  obtain ⟨R, hsmall, hcoreBound⟩ := selectedInputs.remainder
  exact completeClassification_of_split_theta_error_and_integral_core
    h4Y (by linarith) le_rfl finitePrimeCounting finiteTheta
    finiteShortInterval (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hsmall thetaError (by simpa using hcoreBound)

/-! Compact indexed certificates at the selected cutoff.  The certificate
layer supplies one finite family for each bounded estimate; the MediumPNT
tail is supplied separately and the all-`k` conclusion is assembled here. -/
structure MediumPNTSelectedIndexedSplitCertificate (X C : Real) : Prop where
  cutoff : Real
  lower : X ≤ cutoff
  large : (4e18 : Real) ≤ cutoff
  primeCountingRows : ∃ n : Nat, ∃ rows : Fin n → DusartPrimeCountingEndpointRow,
    DusartPrimeCountingEndpointIndexedCoverFrom599 rows cutoff
  thetaRows : ∃ n : Nat, ∃ rows : Fin n → DusartThetaEndpointRow,
    DusartThetaEndpointIndexedCoverUpTo rows cutoff
  logRows : ∃ n : Nat, ∃ rows : Fin n → LogCubedPrimeRow,
    LogCubedPrimeIndexedCoverUpTo rows cutoff
  thetaError : HasThetaLogFourthErrorAbove (648 / 1000 : Real) cutoff
  remainder : ∃ R : Real,
    |∫ t in (2 : Real)..cutoff,
        (Chebyshev.theta t / (t * (Real.log t) ^ 2) -
          1 / (Real.log t) ^ 2)| ≤ R ∧
      4000 + 720 * (∫ t in (2 : Real)..cutoff, 1 / Real.log t ^ 7) + R ≤
        C * cutoff / Real.log cutoff ^ 4

theorem mediumPNTSelectedIndexedSplitCertificate_of_lists
    {X C Y R : Real}
    (hXY : X ≤ Y) (h4Y : (4e18 : Real) ≤ Y)
    {primeRows : List DusartPrimeCountingEndpointRow}
    (primeCover : DusartPrimeCountingEndpointRowsCoverFrom599 primeRows Y)
    {thetaRows : List DusartThetaEndpointRow}
    (thetaCover : DusartThetaEndpointRowsCoverUpTo thetaRows Y)
    {logRows : List LogCubedPrimeRow}
    (logCover : LogCubedPrimeRowsCoverUpTo logRows Y)
    (thetaError : HasThetaLogFourthErrorAbove (648 / 1000 : Real) Y)
    (hsmall :
      |∫ t in (2 : Real)..Y,
          (Chebyshev.theta t / (t * (Real.log t) ^ 2) -
            1 / (Real.log t) ^ 2)| ≤ R)
    (hcore :
      4000 + 720 * (∫ t in (2 : Real)..Y, 1 / Real.log t ^ 7) + R ≤
        C * Y / Real.log Y ^ 4) :
    MediumPNTSelectedIndexedSplitCertificate X C := by
  exact {
    cutoff := Y
    lower := hXY
    large := h4Y
    primeCountingRows := ⟨primeRows.length,
      (fun i => primeRows.get i),
      dusartPrimeCountingEndpointIndexedCover_of_list primeCover⟩
    thetaRows := ⟨thetaRows.length,
      (fun i => thetaRows.get i),
      dusartThetaEndpointIndexedCover_of_list thetaCover⟩
    logRows := ⟨logRows.length,
      (fun i => logRows.get i),
      logCubedPrimeIndexedCover_of_list logCover⟩
    thetaError := thetaError
    remainder := ⟨R, hsmall, hcore⟩ }

theorem completeClassification_of_mediumPNT_and_selected_indexed_split_certificate
    {X C : Real} (hX : (4e18 : Real) ≤ X)
    (hC0 : 0 ≤ C) (hC : C ≤ 3 / 5)
    (certificate : MediumPNTSelectedIndexedSplitCertificate X C) :
    CompleteClassification := by
  obtain ⟨nPrime, primeRows, primeCover⟩ := certificate.primeCountingRows
  obtain ⟨nTheta, thetaRows, thetaCover⟩ := certificate.thetaRows
  obtain ⟨nLog, logRows, logCover⟩ := certificate.logRows
  have finitePrimeCounting :
      HasDusartRealPrimeCountingBoundsBelow certificate.cutoff :=
    hasDusartRealPrimeCountingBoundsBelow_of_indexed_endpoint_rows
      primeCover dusartSmallUpperIntervalRows_provide
  have finiteTheta :
      HasDusartSymmetricThetaBoundsBelow certificate.cutoff :=
    hasDusartSymmetricThetaBoundsBelow_of_indexed_endpoint_rows thetaCover
  have finiteShortInterval :
      HasLogCubedShortIntervalPrimeBelow certificate.cutoff :=
    hasLogCubedShortIntervalPrimeBelow_of_indexed_rows logCover
  exact completeClassification_of_mediumPNT_and_selected_split_inputs hX hC0 hC
    (mediumPNTSelectedSplitInputs_of_cutoff
      certificate.lower certificate.large certificate.thetaError
      finitePrimeCounting finiteTheta finiteShortInterval certificate.remainder)

/-! The finite theta remainder also discharges the Abel-core hypothesis.  This
keeps the all-`k` boundary aligned with the actual finite inputs: the only
remaining provider data are the bounded prime-counting, theta, and interval
facts at the selected cutoff. -/
theorem completeClassification_of_mediumPNT_and_selected_finite_theta_error
    {A X : Real} (hX : (4e18 : Real) ≤ X)
    (hA0 : 0 ≤ A) (hA1 : A ≤ 1)
    (finiteThetaError : HasThetaLogFourthErrorBelow A X)
    (selectedInputs : MediumPNTSelectedFiniteInputs A X) :
    CompleteClassification := by
  have hcore : |primeCountingCore X| ≤
      (3 / 5 : Real) * X / Real.log X ^ 4 :=
    primeCountingCore_abs_le_at_large_cutoff_of_theta_error
      hX hA0 hA1 finiteThetaError
  exact completeClassification_of_mediumPNT_and_selected_finite_inputs
    hX hA0 hA1 (by norm_num) (by norm_num) hcore selectedInputs

/-! This is the certificate boundary for the corrected all-cutoff argument.
Unlike the legacy provider below, it does not ask for the false statement
`|theta x - x| ≤ .648*x/log⁴ x` starting at `2`.  The theta rows begin at the
cutoff supplied by MediumPNT; the finite prefix is represented only by the
Abel-remainder bound. -/
structure MediumPNTFiniteSplitRemainderRowProvider (X C : Real) : Prop where
  primeCountingRows : ∀ Y : Real, X ≤ Y →
    ∃ rows : List DusartPrimeCountingRow,
      DusartPrimeCountingRowsCoverFrom599 rows Y
  primeCountingSmallUpper : ∀ Y : Real, X ≤ Y →
    ∀ x : Real, 2 ≤ x → x < 599 →
      (Nat.primeCounting ⌊x⌋₊ : Real) ≤ dusartPiUpper x
  thetaRows : ∀ Y : Real, X ≤ Y →
    ∃ rows : List DusartThetaBoundsRow,
      DusartThetaBoundsRowsCoverUpTo rows Y
  shortIntervalRows : ∀ Y : Real, X ≤ Y →
    ∃ rows : List LogCubedPrimeRow,
      LogCubedPrimeRowsCoverUpTo rows Y
  remainder : ∀ Y : Real, X ≤ Y →
    ∃ R : Real,
      |∫ t in (2 : Real)..Y,
          (Chebyshev.theta t / (t * (Real.log t) ^ 2) -
            1 / (Real.log t) ^ 2)| ≤ R ∧
      4000 + 720 * (∫ t in (2 : Real)..Y, 1 / Real.log t ^ 7) + R ≤
        C * Y / Real.log Y ^ 4

theorem completeClassification_of_mediumPNT_and_split_remainder_row_provider
    {X C : Real} (hX : (4e18 : Real) ≤ X)
    (hC0 : 0 ≤ C) (hC : C ≤ 3 / 5)
    (provider : MediumPNTFiniteSplitRemainderRowProvider X C) :
    CompleteClassification := by
  apply completeClassification_of_mediumPNT_and_selected_split_inputs hX hC0 hC
  intro Y hXY
  obtain ⟨primeRows, primeCover⟩ := provider.primeCountingRows Y hXY
  obtain ⟨thetaRows, thetaCover⟩ := provider.thetaRows Y hXY
  obtain ⟨shortRows, shortCover⟩ := provider.shortIntervalRows Y hXY
  obtain ⟨R, hR, hcore⟩ := provider.remainder Y hXY
  exact ⟨hasDusartRealPrimeCountingBoundsBelow_of_rows_from599 primeCover
      (provider.primeCountingSmallUpper Y hXY),
    hasDusartSymmetricThetaBoundsBelow_of_rows thetaCover,
      hasLogCubedShortIntervalPrimeBelow_of_rows shortCover,
    R, hR, hcore⟩

/-! The elementary small-prefix estimate can be built into the provider
interface.  This removes even the finite Abel integral from the certificate:
only the explicit large-cutoff inequality remains to be checked. -/
structure MediumPNTFiniteSplitCoreRowProvider (X C : Real) : Prop where
  primeCountingRows : ∀ Y : Real, X ≤ Y →
    ∃ rows : List DusartPrimeCountingRow,
      DusartPrimeCountingRowsCoverFrom599 rows Y
  primeCountingSmallUpper : ∀ Y : Real, X ≤ Y →
    ∀ x : Real, 2 ≤ x → x < 599 →
      (Nat.primeCounting ⌊x⌋₊ : Real) ≤ dusartPiUpper x
  thetaRows : ∀ Y : Real, X ≤ Y →
    ∃ rows : List DusartThetaBoundsRow,
      DusartThetaBoundsRowsCoverUpTo rows Y
  shortIntervalRows : ∀ Y : Real, X ≤ Y →
    ∃ rows : List LogCubedPrimeRow,
      LogCubedPrimeRowsCoverUpTo rows Y
  core : ∀ Y : Real, X ≤ Y →
    4000 + 720 * (∫ t in (2 : Real)..Y, 1 / Real.log t ^ 7) + 10 * Y ≤
      C * Y / Real.log Y ^ 4

theorem completeClassification_of_mediumPNT_and_split_core_row_provider
    {X C : Real} (hX : (4e18 : Real) ≤ X)
    (hC0 : 0 ≤ C) (hC : C ≤ 3 / 5)
    (provider : MediumPNTFiniteSplitCoreRowProvider X C) :
    CompleteClassification := by
  apply completeClassification_of_mediumPNT_and_split_remainder_row_provider
    hX hC0 hC
  refine { primeCountingRows := provider.primeCountingRows
    primeCountingSmallUpper := provider.primeCountingSmallUpper
    thetaRows := provider.thetaRows
    shortIntervalRows := provider.shortIntervalRows
    remainder := ?_ }
  intro Y hXY
  refine ⟨10 * Y, ?_, ?_⟩
  · exact small_integral_remainder_le_ten_mul (by linarith [hX])
  · exact provider.core Y hXY

/-! The fixed grouped table supplies the only small prime-counting field in
the core-row interface.  Large prime-counting, theta, and short-interval
lists remain independent inputs, so each can be generated and checked by its
own compact certificate. -/
theorem completeClassification_of_mediumPNT_and_split_core_rows
    {X C : Real} (hX : (4e18 : Real) ≤ X)
    (hC0 : 0 ≤ C) (hC : C ≤ 3 / 5)
    (primeCountingRows : ∀ Y : Real, X ≤ Y →
      ∃ rows : List DusartPrimeCountingRow,
        DusartPrimeCountingRowsCoverFrom599 rows Y)
    (thetaRows : ∀ Y : Real, X ≤ Y →
      ∃ rows : List DusartThetaBoundsRow,
        DusartThetaBoundsRowsCoverUpTo rows Y)
    (shortIntervalRows : ∀ Y : Real, X ≤ Y →
      ∃ rows : List LogCubedPrimeRow,
        LogCubedPrimeRowsCoverUpTo rows Y)
    (core : ∀ Y : Real, X ≤ Y →
      4000 + 720 * (∫ t in (2 : Real)..Y, 1 / Real.log t ^ 7) + 10 * Y ≤
        C * Y / Real.log Y ^ 4) :
    CompleteClassification := by
  apply completeClassification_of_mediumPNT_and_split_core_row_provider
    hX hC0 hC
  exact {
    primeCountingRows := primeCountingRows
    primeCountingSmallUpper := fun _ _ => dusartSmallUpperIntervalRows_provide
    thetaRows := thetaRows
    shortIntervalRows := shortIntervalRows
    core := core }

/-! Public source-level all-`k` assembly.  The four finite providers are
independent bounded obligations; the unbounded part is proved by the
source-level MediumPNT adapter. -/
theorem completeClassification_of_mediumPNT_and_finite_error_provider
    (finitePrimeCounting : ∀ X : Real, (4e18 : Real) ≤ X →
      HasDusartRealPrimeCountingBoundsBelow X)
    (finiteTheta : ∀ X : Real, (4e18 : Real) ≤ X →
      HasDusartSymmetricThetaBoundsBelow X)
    (finiteShortInterval : ∀ X : Real, (4e18 : Real) ≤ X →
      HasLogCubedShortIntervalPrimeBelow X)
    (finiteThetaError : ∀ X : Real, (4e18 : Real) ≤ X →
      HasThetaLogFourthErrorBelow (648 / 1000 : Real) X) :
    CompleteClassification := by
  obtain ⟨X, _, h4X, _⟩ :=
    exists_hasThetaLogFourthError_of_mediumPNT_above (4e18 : Real)
  obtain ⟨Y, hXY, tailPrimeCounting, _tailThetaBounds, tailThetaError, tailInterval⟩ :=
    exists_mediumPNT_all_real_dusart_tail_inputs_with_theta_bounds
      h4X (by norm_num) (by norm_num) (finiteThetaError X h4X)
  have h4Y : (4e18 : Real) ≤ Y := h4X.trans hXY
  have hYpos : 0 < Y := by linarith
  have hlogY : (42 : Real) ≤ Real.log Y := by
    have hlog_mono : Real.log (4e18 : Real) ≤ Real.log Y :=
      Real.log_le_log (by norm_num) h4Y
    linarith [forty_two_lt_log_four_e18]
  have hthetaErrorY :
      HasThetaLogFourthError (648 / 1000 : Real) Y := by
    intro x hx
    exact tailThetaError x hx
  have hthetaCubic0 :
      HasThetaLogCubedError
        ((648 / 1000 : Real) / Real.log Y) Y :=
    hasThetaLogCubedError_of_logFourthError
      (by linarith [hlogY]) (by norm_num) hthetaErrorY
  have hAlog : (648 / 1000 : Real) / Real.log Y ≤
      (12167 / 500000 : Real) := by
    have hlogYpos : 0 < Real.log Y := by linarith
    apply (div_le_iff₀ hlogYpos).2
    nlinarith [hlogY]
  have thetaErrorCubic :
      HasThetaLogCubedError (12167 / 500000 : Real) Y := by
    intro x hx
    have hbound := hthetaCubic0 x hx
    have hxpos : 0 < x := lt_of_lt_of_le hYpos hx
    have hlogxpos : 0 < Real.log x := by
      have hlogx : (42 : Real) ≤ Real.log x :=
        hlogY.trans (Real.log_le_log hYpos hx)
      linarith
    have hfactor : 0 ≤ x / (Real.log x) ^ 3 := by
      positivity
    calc
      |Chebyshev.theta x - x| ≤
          ((648 / 1000 : Real) / Real.log Y) *
            x / (Real.log x) ^ 3 := hbound
      _ = ((648 / 1000 : Real) / Real.log Y) *
            (x / (Real.log x) ^ 3) := by ring
      _ ≤ (12167 / 500000 : Real) *
            (x / (Real.log x) ^ 3) :=
        mul_le_mul_of_nonneg_right hAlog hfactor
      _ = (12167 / 500000 : Real) * x /
            (Real.log x) ^ 3 := by ring
  exact completeClassification_of_full_record_raised_cutoff_inputs
    h4Y (finitePrimeCounting Y h4Y) tailPrimeCounting
    (finiteTheta Y h4Y) thetaErrorCubic
    (finiteShortInterval Y h4Y) tailInterval

/-! The finite obligations can be supplied directly as bounded row covers.
The row lists may be generated independently for each selected cutoff; this
keeps the theorem independent of certificate representation while making all
four finite obligations explicit. -/
theorem completeClassification_of_mediumPNT_and_row_provider
    (finitePrimeCountingRows : ∀ X : Real, (4e18 : Real) ≤ X →
      ∃ rows : List DusartPrimeCountingRow,
        DusartPrimeCountingRowsCoverUpTo rows X)
    (finiteThetaRows : ∀ X : Real, (4e18 : Real) ≤ X →
      ∃ rows : List DusartThetaBoundsRow,
        DusartThetaBoundsRowsCoverUpTo rows X)
    (finiteShortIntervalRows : ∀ X : Real, (4e18 : Real) ≤ X →
      ∃ rows : List LogCubedPrimeRow,
        LogCubedPrimeRowsCoverUpTo rows X)
    (finiteThetaErrorRows : ∀ X : Real, (4e18 : Real) ≤ X →
      ∃ rows : List (ThetaLogFourthErrorRow (648 / 1000 : Real)),
        ThetaLogFourthErrorRowsCoverUpTo rows X) :
    CompleteClassification := by
  refine completeClassification_of_mediumPNT_and_finite_error_provider
    (fun X hX => ?_) (fun X hX => ?_) (fun X hX => ?_) (fun X hX => ?_)
  · obtain ⟨rows, cover⟩ := finitePrimeCountingRows X hX
    exact hasDusartRealPrimeCountingBoundsBelow_of_rows cover
  · obtain ⟨rows, cover⟩ := finiteThetaRows X hX
    exact hasDusartSymmetricThetaBoundsBelow_of_rows cover
  · obtain ⟨rows, cover⟩ := finiteShortIntervalRows X hX
    exact hasLogCubedShortIntervalPrimeBelow_of_rows cover
  · obtain ⟨rows, cover⟩ := finiteThetaErrorRows X hX
    exact hasThetaLogFourthErrorBelow_of_rows cover

/-! A bundled version of the same boundary is convenient for the final
certificate-producing layer.  It is a proposition, so packaging it does not
introduce data or an additional computational assumption. -/
structure MediumPNTFiniteRowProvider : Prop where
  primeCountingRows : ∀ X : Real, (4e18 : Real) ≤ X →
    ∃ rows : List DusartPrimeCountingRow,
      DusartPrimeCountingRowsCoverUpTo rows X
  thetaRows : ∀ X : Real, (4e18 : Real) ≤ X →
    ∃ rows : List DusartThetaBoundsRow,
      DusartThetaBoundsRowsCoverUpTo rows X
  shortIntervalRows : ∀ X : Real, (4e18 : Real) ≤ X →
    ∃ rows : List LogCubedPrimeRow,
      LogCubedPrimeRowsCoverUpTo rows X
  thetaErrorRows : ∀ X : Real, (4e18 : Real) ≤ X →
    ∃ rows : List (ThetaLogFourthErrorRow (648 / 1000 : Real)),
      ThetaLogFourthErrorRowsCoverUpTo rows X

theorem completeClassification_of_mediumPNT_and_bundled_row_provider
    (provider : MediumPNTFiniteRowProvider) :
    CompleteClassification := by
  exact completeClassification_of_mediumPNT_and_row_provider
    provider.primeCountingRows provider.thetaRows
    provider.shortIntervalRows provider.thetaErrorRows

/-! A split prime-counting provider avoids certifying the lower Dusart
inequality below `599`, where it is not required. -/
private structure MediumPNTFiniteSplitRowProvider : Prop where
  primeCountingRows : ∀ X : Real, (4e18 : Real) ≤ X →
    ∃ rows : List DusartPrimeCountingRow,
      DusartPrimeCountingRowsCoverFrom599 rows X
  primeCountingSmallUpper : ∀ X : Real, (4e18 : Real) ≤ X →
    ∀ x : Real, 2 ≤ x → x < 599 →
      (Nat.primeCounting ⌊x⌋₊ : Real) ≤ dusartPiUpper x
  thetaRows : ∀ X : Real, (4e18 : Real) ≤ X →
    ∃ rows : List DusartThetaBoundsRow,
      DusartThetaBoundsRowsCoverUpTo rows X
  shortIntervalRows : ∀ X : Real, (4e18 : Real) ≤ X →
    ∃ rows : List LogCubedPrimeRow,
      LogCubedPrimeRowsCoverUpTo rows X
  thetaErrorRows : ∀ X : Real, (4e18 : Real) ≤ X →
    ∃ rows : List (ThetaLogFourthErrorRow (648 / 1000 : Real)),
      ThetaLogFourthErrorRowsCoverUpTo rows X

private theorem completeClassification_of_mediumPNT_and_split_row_provider
    (provider : MediumPNTFiniteSplitRowProvider) :
    CompleteClassification := by
  refine completeClassification_of_mediumPNT_and_finite_error_provider
    (fun X hX => ?_) (fun X hX => ?_) (fun X hX => ?_) (fun X hX => ?_)
  · obtain ⟨rows, hcover⟩ := provider.primeCountingRows X hX
    exact hasDusartRealPrimeCountingBoundsBelow_of_rows_from599 hcover
      (provider.primeCountingSmallUpper X hX)
  · obtain ⟨rows, hcover⟩ := provider.thetaRows X hX
    exact hasDusartSymmetricThetaBoundsBelow_of_rows hcover
  · obtain ⟨rows, hcover⟩ := provider.shortIntervalRows X hX
    exact hasLogCubedShortIntervalPrimeBelow_of_rows hcover
  · obtain ⟨rows, hcover⟩ := provider.thetaErrorRows X hX
    exact hasThetaLogFourthErrorBelow_of_rows hcover

/-! The integer-floor form is the compact certificate boundary for the small
prime-counting range. -/
private structure MediumPNTFiniteIntegerSplitRowProvider : Prop where
  primeCountingRows : ∀ X : Real, (4e18 : Real) ≤ X →
    ∃ rows : List DusartPrimeCountingEndpointRow,
      DusartPrimeCountingEndpointRowsCoverFrom599 rows X
  primeCountingSmallIntegerRows : List DusartPrimeCountingUpperIntegerRow
  primeCountingSmallIntegerCover :
    DusartPrimeCountingUpperIntegerRowsCover
      primeCountingSmallIntegerRows
  thetaEndpointRows : ∀ X : Real, (4e18 : Real) ≤ X →
    ∃ rows : List DusartThetaEndpointRow,
      DusartThetaEndpointRowsCoverUpTo rows X
  shortIntervalRows : ∀ X : Real, (4e18 : Real) ≤ X →
    ∃ rows : List LogCubedPrimeRow,
      LogCubedPrimeRowsCoverUpTo rows X
  thetaErrorEndpointRows : ∀ X : Real, (4e18 : Real) ≤ X →
    ∃ rows : List (ThetaLogFourthEndpointRow (648 / 1000 : Real)),
      ThetaLogFourthEndpointRowsCoverUpTo rows X

private theorem completeClassification_of_mediumPNT_and_integer_split_row_provider
    (provider : MediumPNTFiniteIntegerSplitRowProvider) :
    CompleteClassification := by
  refine completeClassification_of_mediumPNT_and_finite_error_provider
    (fun X hX => ?_) (fun X hX => ?_) (fun X hX => ?_) (fun X hX => ?_)
  · obtain ⟨rows, hcover⟩ := provider.primeCountingRows X hX
    exact hasDusartRealPrimeCountingBoundsBelow_of_endpoint_rows hcover
      (real_primeCounting_upper_of_integer_rows
        provider.primeCountingSmallIntegerCover)
  · obtain ⟨rows, hcover⟩ := provider.thetaEndpointRows X hX
    exact hasDusartSymmetricThetaBoundsBelow_of_endpoint_rows hcover
  · obtain ⟨rows, hcover⟩ := provider.shortIntervalRows X hX
    exact hasLogCubedShortIntervalPrimeBelow_of_rows hcover
  · obtain ⟨rows, hcover⟩ := provider.thetaErrorEndpointRows X hX
    exact hasThetaLogFourthErrorBelow_of_endpoint_rows (by norm_num) hcover

/-! The small prime-counting part can also be supplied by interval rows.  This
form is deliberately separate from the point-row provider so existing data
remains reusable while new certificates can group consecutive integer checks.
-/
private structure MediumPNTFiniteIntegerIntervalSplitRowProvider : Prop where
  primeCountingRows : ∀ X : Real, (4e18 : Real) ≤ X →
    ∃ rows : List DusartPrimeCountingEndpointRow,
      DusartPrimeCountingEndpointRowsCoverFrom599 rows X
  primeCountingSmallIntegerIntervalRows :
    List DusartPrimeCountingUpperIntegerIntervalRow
  primeCountingSmallIntegerIntervalCover :
    DusartPrimeCountingUpperIntegerIntervalRowsCover
      primeCountingSmallIntegerIntervalRows
  thetaEndpointRows : ∀ X : Real, (4e18 : Real) ≤ X →
    ∃ rows : List DusartThetaEndpointRow,
      DusartThetaEndpointRowsCoverUpTo rows X
  shortIntervalRows : ∀ X : Real, (4e18 : Real) ≤ X →
    ∃ rows : List LogCubedPrimeRow,
      LogCubedPrimeRowsCoverUpTo rows X
  thetaErrorEndpointRows : ∀ X : Real, (4e18 : Real) ≤ X →
    ∃ rows : List (ThetaLogFourthEndpointRow (648 / 1000 : Real)),
      ThetaLogFourthEndpointRowsCoverUpTo rows X

private theorem completeClassification_of_mediumPNT_and_integer_interval_split_row_provider
    (provider : MediumPNTFiniteIntegerIntervalSplitRowProvider) :
    CompleteClassification := by
  refine completeClassification_of_mediumPNT_and_finite_error_provider
    (fun X hX => ?_) (fun X hX => ?_) (fun X hX => ?_) (fun X hX => ?_)
  · obtain ⟨rows, hcover⟩ := provider.primeCountingRows X hX
    exact hasDusartRealPrimeCountingBoundsBelow_of_endpoint_rows hcover
      (real_primeCounting_upper_of_integer_interval_rows
        provider.primeCountingSmallIntegerIntervalCover)
  · obtain ⟨rows, hcover⟩ := provider.thetaEndpointRows X hX
    exact hasDusartSymmetricThetaBoundsBelow_of_endpoint_rows hcover
  · obtain ⟨rows, hcover⟩ := provider.shortIntervalRows X hX
    exact hasLogCubedShortIntervalPrimeBelow_of_rows hcover
  · obtain ⟨rows, hcover⟩ := provider.thetaErrorEndpointRows X hX
    exact hasThetaLogFourthErrorBelow_of_endpoint_rows (by norm_num) hcover

/-! The compact small-prime table is fixed data, so callers supplying the
large endpoint tables should not have to repeat its list or its cover. -/
/-! Compact all-`k` finite boundary.  The small prime-counting interval table
is fixed below; callers provide only the large-cutoff endpoint families. -/
structure MediumPNTFiniteIntegerIntervalTailProvider : Prop where
  primeCountingRows : ∀ X : Real, (4e18 : Real) ≤ X →
    ∃ rows : List DusartPrimeCountingEndpointRow,
      DusartPrimeCountingEndpointRowsCoverFrom599 rows X
  thetaEndpointRows : ∀ X : Real, (4e18 : Real) ≤ X →
    ∃ rows : List DusartThetaEndpointRow,
      DusartThetaEndpointRowsCoverUpTo rows X
  shortIntervalRows : ∀ X : Real, (4e18 : Real) ≤ X →
    ∃ rows : List LogCubedPrimeRow,
      LogCubedPrimeRowsCoverUpTo rows X
  thetaErrorEndpointRows : ∀ X : Real, (4e18 : Real) ≤ X →
    ∃ rows : List (ThetaLogFourthEndpointRow (648 / 1000 : Real)),
      ThetaLogFourthEndpointRowsCoverUpTo rows X

theorem completeClassification_of_mediumPNT_and_integer_interval_tail_provider
    (provider : MediumPNTFiniteIntegerIntervalTailProvider) :
    CompleteClassification := by
  exact completeClassification_of_mediumPNT_and_integer_interval_split_row_provider
    { primeCountingRows := provider.primeCountingRows
      primeCountingSmallIntegerIntervalRows := dusartSmallUpperIntervalRows
      primeCountingSmallIntegerIntervalCover := dusartSmallUpperIntervalRows_cover
      thetaEndpointRows := provider.thetaEndpointRows
      shortIntervalRows := provider.shortIntervalRows
      thetaErrorEndpointRows := provider.thetaErrorEndpointRows }

/-! Indexed certificates are an equivalent presentation of the compact
endpoint boundary.  Keeping this adapter here means a certificate generator
can expose one finite function family per cutoff without materializing a
separate declaration for every row. -/
structure MediumPNTFiniteIntegerIntervalIndexedTailProvider : Prop where
  primeCountingRows : ∀ X : Real, (4e18 : Real) ≤ X →
    ∃ n : Nat, ∃ rows : Fin n → DusartPrimeCountingEndpointRow,
      DusartPrimeCountingEndpointIndexedCoverFrom599 rows X
  thetaEndpointRows : ∀ X : Real, (4e18 : Real) ≤ X →
    ∃ n : Nat, ∃ rows : Fin n → DusartThetaEndpointRow,
      DusartThetaEndpointIndexedCoverUpTo rows X
  shortIntervalRows : ∀ X : Real, (4e18 : Real) ≤ X →
    ∃ n : Nat, ∃ rows : Fin n → LogCubedPrimeRow,
      LogCubedPrimeIndexedCoverUpTo rows X
  thetaErrorEndpointRows : ∀ X : Real, (4e18 : Real) ≤ X →
    ∃ n : Nat, ∃ rows : Fin n →
      ThetaLogFourthEndpointRow (648 / 1000 : Real),
      ThetaLogFourthEndpointIndexedCoverUpTo rows X

theorem completeClassification_of_mediumPNT_and_integer_interval_indexed_tail_provider
    (provider : MediumPNTFiniteIntegerIntervalIndexedTailProvider) :
    CompleteClassification := by
  apply completeClassification_of_mediumPNT_and_integer_interval_tail_provider
  refine {
    primeCountingRows := fun X hX => ?_
    thetaEndpointRows := fun X hX => ?_
    shortIntervalRows := fun X hX => ?_
    thetaErrorEndpointRows := fun X hX => ?_ }
  · obtain ⟨n, rows, hcover⟩ := provider.primeCountingRows X hX
    refine ⟨List.ofFn rows, ?_⟩
    intro x hx hX'
    obtain ⟨i, hleft, hright⟩ := hcover x hx hX'
    exact ⟨rows i, List.mem_ofFn.mpr ⟨i, rfl⟩, hleft, hright⟩
  · obtain ⟨n, rows, hcover⟩ := provider.thetaEndpointRows X hX
    refine ⟨List.ofFn rows, ?_⟩
    intro x hx hX'
    obtain ⟨i, hleft, hright⟩ := hcover x hx hX'
    exact ⟨rows i, List.mem_ofFn.mpr ⟨i, rfl⟩, hleft, hright⟩
  · obtain ⟨n, rows, hcover⟩ := provider.shortIntervalRows X hX
    refine ⟨List.ofFn rows, ?_⟩
    intro x hx hX'
    obtain ⟨i, hleft, hright⟩ := hcover x hx hX'
    exact ⟨rows i, List.mem_ofFn.mpr ⟨i, rfl⟩, hleft, hright⟩
  · obtain ⟨n, rows, hcover⟩ := provider.thetaErrorEndpointRows X hX
    refine ⟨List.ofFn rows, ?_⟩
    intro x hx hX'
    obtain ⟨i, hleft, hright⟩ := hcover x hx hX'
    exact ⟨rows i, List.mem_ofFn.mpr ⟨i, rfl⟩, hleft, hright⟩

/-! A prefix-family presentation is useful when the same ordered certificate
table is queried at many cutoffs.  The rows themselves occur once as
`Nat → row`; each cutoff supplies only the finite prefix that covers it. -/
structure MediumPNTFiniteIntegerIntervalPrefixProvider : Prop where
  primeCountingRows : Nat → DusartPrimeCountingEndpointRow
  primeCountingPrefix : ∀ X : Real, (4e18 : Real) ≤ X →
    ∃ n : Nat,
      DusartPrimeCountingEndpointIndexedCoverFrom599
        (fun i : Fin n => primeCountingRows i) X
  thetaEndpointRows : Nat → DusartThetaEndpointRow
  thetaEndpointPrefix : ∀ X : Real, (4e18 : Real) ≤ X →
    ∃ n : Nat,
      DusartThetaEndpointIndexedCoverUpTo
        (fun i : Fin n => thetaEndpointRows i) X
  shortIntervalRows : Nat → LogCubedPrimeRow
  shortIntervalPrefix : ∀ X : Real, (4e18 : Real) ≤ X →
    ∃ n : Nat,
      LogCubedPrimeIndexedCoverUpTo
        (fun i : Fin n => shortIntervalRows i) X
  thetaErrorEndpointRows : Nat →
    ThetaLogFourthEndpointRow (648 / 1000 : Real)
  thetaErrorEndpointPrefix : ∀ X : Real, (4e18 : Real) ≤ X →
    ∃ n : Nat,
      ThetaLogFourthEndpointIndexedCoverUpTo
        (fun i : Fin n => thetaErrorEndpointRows i) X

theorem completeClassification_of_mediumPNT_and_integer_interval_prefix_provider
    (provider : MediumPNTFiniteIntegerIntervalPrefixProvider) :
    CompleteClassification := by
  apply completeClassification_of_mediumPNT_and_integer_interval_indexed_tail_provider
  exact {
    primeCountingRows := fun X hX => provider.primeCountingPrefix X hX
    thetaEndpointRows := fun X hX => provider.thetaEndpointPrefix X hX
    shortIntervalRows := fun X hX => provider.shortIntervalPrefix X hX
    thetaErrorEndpointRows := fun X hX => provider.thetaErrorEndpointPrefix X hX }

/-! A bundled prefix family is the compact certificate boundary for generators
that compute all four endpoint estimates from the same ordered partition.
The partition is stored once; only its finite prefix length varies with the
cutoff. -/
structure MediumPNTFiniteIntegerIntervalPrefixBundle where
  primeCounting : DusartPrimeCountingEndpointRow
  theta : DusartThetaEndpointRow
  shortInterval : LogCubedPrimeRow
  thetaError : ThetaLogFourthEndpointRow (648 / 1000 : Real)

structure MediumPNTFiniteIntegerIntervalPrefixBundleCover
    {n : Nat} (rows : Fin n → MediumPNTFiniteIntegerIntervalPrefixBundle) (X : Real) : Prop where
  primeCounting : DusartPrimeCountingEndpointIndexedCoverFrom599
    (fun i => (rows i).primeCounting) X
  theta : DusartThetaEndpointIndexedCoverUpTo
    (fun i => (rows i).theta) X
  shortInterval : LogCubedPrimeIndexedCoverUpTo
    (fun i => (rows i).shortInterval) X
  thetaError : ThetaLogFourthEndpointIndexedCoverUpTo
    (fun i => (rows i).thetaError) X

structure MediumPNTFiniteIntegerIntervalBundledPrefixProvider : Prop where
  rows : Nat → MediumPNTFiniteIntegerIntervalPrefixBundle
  prefix : ∀ X : Real, (4e18 : Real) ≤ X →
    ∃ n : Nat,
      MediumPNTFiniteIntegerIntervalPrefixBundleCover
        (fun i : Fin n => rows i) X

theorem completeClassification_of_mediumPNT_and_integer_interval_bundled_prefix_provider
    (provider : MediumPNTFiniteIntegerIntervalBundledPrefixProvider) :
    CompleteClassification := by
  apply completeClassification_of_mediumPNT_and_integer_interval_prefix_provider
  exact {
    primeCountingRows := fun i => (provider.rows i).primeCounting
    primeCountingPrefix := fun X hX => by
      obtain ⟨n, hcover⟩ := provider.prefix X hX
      exact ⟨n, hcover.primeCounting⟩
    thetaEndpointRows := fun i => (provider.rows i).theta
    thetaEndpointPrefix := fun X hX => by
      obtain ⟨n, hcover⟩ := provider.prefix X hX
      exact ⟨n, hcover.theta⟩
    shortIntervalRows := fun i => (provider.rows i).shortInterval
    shortIntervalPrefix := fun X hX => by
      obtain ⟨n, hcover⟩ := provider.prefix X hX
      exact ⟨n, hcover.shortInterval⟩
    thetaErrorEndpointRows := fun i => (provider.rows i).thetaError
    thetaErrorEndpointPrefix := fun X hX => by
      obtain ⟨n, hcover⟩ := provider.prefix X hX
      exact ⟨n, hcover.thetaError⟩ }

/-! The tail prime-counting obligation can equivalently be supplied in the
published asymptotic form.  The adapter is proved in the analytic helper, so
this theorem exposes the exact provider boundary without hiding a new axiom
inside the all-`k` assembly. -/
theorem completeClassification_of_full_record_asymptotic_tail_inputs
    (finitePrimeCounting : HasDusartRealPrimeCountingBoundsBelow (4e18 : Real))
    (asymptotic : HasDusartPrimeCountingAsymptoticAbove (4e9 : Real))
    (finiteTheta : HasDusartSymmetricThetaBoundsBelow (4e18 : Real))
    {rows : List LogCubedPrimeRow}
    (cover : LogCubedPrimeRowsCoverUpTo rows (4e18 : Real))
    (thetaError : HasThetaLogCubedError (12167 / 500000 : Real) (4e18 : Real)) :
    CompleteClassification := by
  exact completeClassification_of_full_record_rows_and_finite_theta
    (hasDusartRealPrimeCountingBounds_of_finite_and_asymptotic
      finitePrimeCounting asymptotic)
    finiteTheta cover thetaError

/-! The tail can be supplied directly by the kernel-checked Abel argument.
This is the all-cutoff boundary used by the eventual explicit provider: no
pre-packaged Dusart asymptotic is assumed here. -/
theorem completeClassification_of_full_record_core_theta_error_inputs
    (finitePrimeCounting : HasDusartRealPrimeCountingBoundsBelow (4e18 : Real))
    {A C X : Real} (hXpos : 0 < X) (h2X : 2 ≤ X)
    (hXcutoff : X ≤ (4e18 : Real))
    (hA0 : 0 ≤ A) (hA : A ≤ 1)
    (hC0 : 0 ≤ C) (hC : C ≤ 3 / 5)
    (hlog : (42 : Real) ≤ Real.log X)
    (hcore : |primeCountingCore X| ≤ C * X / Real.log X ^ 4)
    (coreThetaError : HasThetaLogFourthError A X)
    (finiteTheta : HasDusartSymmetricThetaBoundsBelow (4e18 : Real))
    {rows : List LogCubedPrimeRow}
    (cover : LogCubedPrimeRowsCoverUpTo rows (4e18 : Real))
    (thetaError : HasThetaLogCubedError (12167 / 500000 : Real) (4e18 : Real)) :
    CompleteClassification := by
  exact completeClassification_of_full_record_rows_and_finite_theta
    (hasDusartRealPrimeCountingBounds_of_finite_and_core_and_theta_error
      finitePrimeCounting hXpos h2X hXcutoff hA0 hA hC0 hC hlog hcore
      coreThetaError)
    finiteTheta cover thetaError

/-! Once the finite theta and interval rows are supplied, every analytic
interface is now discharged by the explicit proofs above. -/
theorem completeClassification_of_full_record_explicit_dusart_inputs
    (finitePrimeCounting : HasDusartRealPrimeCountingBoundsBelow (4e18 : Real))
    {A C X : Real} (hXpos : 0 < X) (h2X : 2 ≤ X)
    (hXcutoff : X ≤ (4e18 : Real))
    (hA0 : 0 ≤ A) (hA : A ≤ 1)
    (hC0 : 0 ≤ C) (hC : C ≤ 3 / 5)
    (hlog : (42 : Real) ≤ Real.log X)
    (hcore : |primeCountingCore X| ≤ C * X / Real.log X ^ 4)
    (coreThetaError : HasThetaLogFourthError A X)
    (finiteTheta : HasDusartSymmetricThetaBoundsBelow (4e18 : Real))
    {dusartRows : List DusartPrimeRow}
    (dusartCover : DusartPrimeRowsCoverBelow dusartRows)
    {logRows : List LogCubedPrimeRow}
    (logCover : LogCubedPrimeRowsCoverUpTo logRows (4e18 : Real))
    (thetaError : HasThetaLogCubedError (12167 / 500000 : Real) (4e18 : Real)) :
    CompleteClassification := by
  exact completeClassification_of_full_record_short_interval_inputs
    (hasDusartRealPrimeCountingBounds_of_finite_and_core_and_theta_error
      finitePrimeCounting hXpos h2X hXcutoff hA0 hA hC0 hC hlog hcore
      coreThetaError)
    (hasDusartThetaBounds_of_symmetric
      (hasDusartSymmetricThetaBounds_of_below_and_logCubed
        finiteTheta thetaError))
    (hasDusartShortIntervalPrime_of_rows_and_thetaError
      dusartCover logCover thetaError)

/-! At the paper's stated cutoff, the same log-fourth theta estimate feeds all
three Dusart interfaces: theta bounds, prime counting, and short intervals. -/
theorem completeClassification_of_full_record_unit_logFourth_inputs
    (finitePrimeCounting : HasDusartRealPrimeCountingBoundsBelow (4e18 : Real))
    (finiteTheta : HasDusartSymmetricThetaBoundsBelow (4e18 : Real))
    {A C : Real} (hA0 : 0 ≤ A) (hA : A ≤ 1)
    (hC0 : 0 ≤ C) (hC : C ≤ 3 / 5)
    (hcore : |primeCountingCore (4e18 : Real)| ≤
      C * (4e18 : Real) / Real.log (4e18 : Real) ^ 4)
    (thetaError : HasThetaLogFourthError A (4e18 : Real))
    (hA_log : A / Real.log (4e18 : Real) ≤ 12167 / 500000)
    {dusartRows : List DusartPrimeRow}
    (dusartCover : DusartPrimeRowsCoverBelow dusartRows)
    {logRows : List LogCubedPrimeRow}
    (logCover : LogCubedPrimeRowsCoverUpTo logRows (4e18 : Real)) :
    CompleteClassification := by
  have hlog42 : (42 : Real) ≤ Real.log (4e18 : Real) :=
    forty_two_lt_log_four_e18.le
  have cubic : HasThetaLogCubedError
      (12167 / 500000 : Real) (4e18 : Real) :=
    hasThetaLogCubedError_of_logFourthError
      (by norm_num) hA0 thetaError
  exact completeClassification_of_full_record_short_interval_inputs
    (hasDusartRealPrimeCountingBounds_of_finite_and_core_and_theta_error
      finitePrimeCounting (by norm_num) (by norm_num) le_rfl
      hA0 hA hC0 hC hlog42 hcore thetaError)
    (hasDusartThetaBounds_of_finite_and_logFourth_from
      (by norm_num) (log_large_x_gt_ten le_rfl) finiteTheta hA0 hA_log
      thetaError)
    (hasDusartShortIntervalPrime_of_rows_and_thetaError
      dusartCover logCover cubic)

/-! Exact fixed-cutoff certificate boundary for the paper's all-`k` proof.
The theta rows certify only the finite Dusart bounds; `thetaError` is the
separate log-fourth tail estimate used above the cutoff. -/
private structure DusartFiniteCertificate (A C : Real) : Prop where
  primeCountingRows : List DusartPrimeCountingEndpointRow
  primeCountingCover :
    DusartPrimeCountingEndpointRowsCoverFrom599
      primeCountingRows (4e18 : Real)
  thetaRows : List DusartThetaEndpointRow
  thetaCover :
    DusartThetaEndpointRowsCoverUpTo thetaRows (4e18 : Real)
  dusartShortRows : List DusartPrimeRow
  dusartShortCover : DusartPrimeRowsCoverBelow dusartShortRows
  logRows : List LogCubedPrimeRow
  logCover : LogCubedPrimeRowsCoverUpTo logRows (4e18 : Real)
  hA0 : 0 ≤ A
  hA1 : A ≤ 1
  hA_log : A / Real.log (4e18 : Real) ≤ 12167 / 500000
  hC0 : 0 ≤ C
  hC : C ≤ 3 / 5
  hcore : |primeCountingCore (4e18 : Real)| ≤
    C * (4e18 : Real) / Real.log (4e18 : Real) ^ 4
  thetaError : HasThetaLogFourthError A (4e18 : Real)

private theorem completeClassification_of_dusart_finite_certificate
    {A C : Real} (certificate : DusartFiniteCertificate A C) :
    CompleteClassification := by
  exact completeClassification_of_full_record_unit_logFourth_inputs
    (hasDusartRealPrimeCountingBoundsBelow_of_endpoint_rows
      certificate.primeCountingCover dusartSmallUpperIntervalRows_provide)
    (hasDusartSymmetricThetaBoundsBelow_of_endpoint_rows
      certificate.thetaCover)
    certificate.hA0 certificate.hA1 certificate.hC0 certificate.hC
    certificate.hcore certificate.thetaError certificate.hA_log
    certificate.dusartShortCover certificate.logCover

/-! Split certificate boundary with no opaque finite core theorem.  The sharp
theta table starts at `x₀`; its prefix contributes only `smallRemainder`, and
`thetaTail` is the valid analytic estimate beginning at the fixed cutoff. -/
structure DusartSplitFiniteCertificate (A C x₀ R : Real) : Prop where
  primeCountingRows : List DusartPrimeCountingEndpointRow
  primeCountingCover :
    DusartPrimeCountingEndpointRowsCoverFrom599
      primeCountingRows (4e18 : Real)
  thetaRows : List DusartThetaEndpointRow
  thetaCover :
    DusartThetaEndpointRowsCoverUpTo thetaRows (4e18 : Real)
  logRows : List LogCubedPrimeRow
  logCover : LogCubedPrimeRowsCoverUpTo logRows (4e18 : Real)
  thetaErrorRows : List (ThetaLogFourthEndpointRow A)
  thetaErrorCover :
    ThetaLogFourthEndpointRowsCoverFrom thetaErrorRows x₀ (4e18 : Real)
  thetaTail : HasThetaLogFourthErrorAbove A (4e18 : Real)
  h2x₀ : (2 : Real) ≤ x₀
  hx₀ : x₀ ≤ (4e18 : Real)
  smallRemainder :
    |∫ t in (2 : Real)..x₀,
        (Chebyshev.theta t / (t * (Real.log t) ^ 2) -
          1 / (Real.log t) ^ 2)| ≤ R
  hA0 : 0 ≤ A
  hA1 : A ≤ 1
  hC0 : 0 ≤ C
  hC : C ≤ 3 / 5
  integralCoreBound :
    4000 + 720 * (∫ t in (2 : Real)..(4e18 : Real),
        1 / Real.log t ^ 7) + R +
        A * (∫ t in x₀..(4e18 : Real), 1 / Real.log t ^ 6) ≤
      C * (4e18 : Real) / Real.log (4e18 : Real) ^ 4

theorem completeClassification_of_dusart_split_finite_certificate
    {A C x₀ : Real}
    (certificate : DusartSplitFiniteCertificate A C x₀) :
    CompleteClassification := by
  have finitePrimeCounting :
      HasDusartRealPrimeCountingBoundsBelow (4e18 : Real) :=
    hasDusartRealPrimeCountingBoundsBelow_of_endpoint_rows
      certificate.primeCountingCover dusartSmallUpperIntervalRows_provide
  have finiteTheta :
      HasDusartSymmetricThetaBoundsBelow (4e18 : Real) :=
    hasDusartSymmetricThetaBoundsBelow_of_endpoint_rows
      certificate.thetaCover
  have finiteShortInterval :
      HasLogCubedShortIntervalPrimeBelow (4e18 : Real) :=
    hasLogCubedShortIntervalPrimeBelow_of_rows certificate.logCover
  have thetaErrorAbove : HasThetaLogFourthErrorAbove A x₀ :=
    hasThetaLogFourthErrorAbove_of_endpoint_rows_from_and_tail
      certificate.hA0 certificate.thetaErrorCover certificate.thetaTail
  exact completeClassification_of_split_theta_error_and_integral_core
    (by norm_num) certificate.h2x₀ certificate.hx₀ finitePrimeCounting
    finiteTheta finiteShortInterval certificate.hA0 certificate.hA1
    certificate.hC0 certificate.hC certificate.smallRemainder thetaErrorAbove
    certificate.integralCoreBound

structure Dusart599SplitFiniteCertificate (A C : Real) : Prop where
  primeCountingRows : List DusartPrimeCountingEndpointRow
  primeCountingCover :
    DusartPrimeCountingEndpointRowsCoverFrom599
      primeCountingRows (4e18 : Real)
  thetaRows : List DusartThetaEndpointRow
  thetaCover :
    DusartThetaEndpointRowsCoverUpTo thetaRows (4e18 : Real)
  logRows : List LogCubedPrimeRow
  logCover : LogCubedPrimeRowsCoverUpTo logRows (4e18 : Real)
  thetaErrorRows : List (ThetaLogFourthEndpointRow A)
  thetaErrorCover :
    ThetaLogFourthEndpointRowsCoverFrom thetaErrorRows 599 (4e18 : Real)
  thetaTail : HasThetaLogFourthErrorAbove A (4e18 : Real)
  hA0 : 0 ≤ A
  hA1 : A ≤ 1
  hC0 : 0 ≤ C
  hC : C ≤ 3 / 5
  integralCoreBound :
    4000 + 720 * (∫ t in (2 : Real)..(4e18 : Real),
        1 / Real.log t ^ 7) + 10000 +
        A * (∫ t in (599 : Real)..(4e18 : Real),
          1 / Real.log t ^ 6) ≤
      C * (4e18 : Real) / Real.log (4e18 : Real) ^ 4

theorem completeClassification_of_dusart_599_split_finite_certificate
    {A C : Real}
    (certificate : Dusart599SplitFiniteCertificate A C) :
    CompleteClassification := by
  have finitePrimeCounting :
      HasDusartRealPrimeCountingBoundsBelow (4e18 : Real) :=
    hasDusartRealPrimeCountingBoundsBelow_of_endpoint_rows
      certificate.primeCountingCover dusartSmallUpperIntervalRows_provide
  have finiteTheta :
      HasDusartSymmetricThetaBoundsBelow (4e18 : Real) :=
    hasDusartSymmetricThetaBoundsBelow_of_endpoint_rows
      certificate.thetaCover
  have finiteShortInterval :
      HasLogCubedShortIntervalPrimeBelow (4e18 : Real) :=
    hasLogCubedShortIntervalPrimeBelow_of_rows certificate.logCover
  have thetaErrorAbove : HasThetaLogFourthErrorAbove A (599 : Real) :=
    hasThetaLogFourthErrorAbove_of_endpoint_rows_from_and_tail
      certificate.hA0 certificate.thetaErrorCover certificate.thetaTail
  apply completeClassification_of_split_theta_error_and_reserved_integral_core
    (x₀ := (599 : Real)) (R := 10 * (599 : Real))
  · norm_num
  · norm_num
  · exact finitePrimeCounting
  · exact finiteTheta
  · exact finiteShortInterval
  · exact certificate.hA0
  · exact certificate.hA1
  · exact certificate.hC0
  · exact certificate.hC
  · exact small_integral_remainder_le_5990
  · norm_num
  · exact thetaErrorAbove
  · exact certificate.integralCoreBound

/-! Fixed-cutoff certificate boundary with the analytic core discharged by
the explicit Abel estimate.  The remaining fields are exactly the finite
Dusart rows and the eventual theta-error tail. -/
structure Dusart599FiniteCertificate (A : Real) : Prop where
  primeCountingRows : List DusartPrimeCountingEndpointRow
  primeCountingCover :
    DusartPrimeCountingEndpointRowsCoverFrom599
      primeCountingRows (4e18 : Real)
  thetaRows : List DusartThetaEndpointRow
  thetaCover :
    DusartThetaEndpointRowsCoverUpTo thetaRows (4e18 : Real)
  logRows : List LogCubedPrimeRow
  logCover : LogCubedPrimeRowsCoverUpTo logRows (4e18 : Real)
  thetaErrorRows : List (ThetaLogFourthEndpointRow A)
  thetaErrorCover :
    ThetaLogFourthEndpointRowsCoverFrom thetaErrorRows 599 (4e18 : Real)
  thetaTail : HasThetaLogFourthErrorAbove A (4e18 : Real)
  hA0 : 0 ≤ A
  hA1 : A ≤ 1

theorem completeClassification_of_dusart_599_finite_certificate
    {A : Real} (certificate : Dusart599FiniteCertificate A) :
    CompleteClassification := by
  have finitePrimeCounting :
      HasDusartRealPrimeCountingBoundsBelow (4e18 : Real) :=
    hasDusartRealPrimeCountingBoundsBelow_of_endpoint_rows
      certificate.primeCountingCover dusartSmallUpperIntervalRows_provide
  have finiteTheta :
      HasDusartSymmetricThetaBoundsBelow (4e18 : Real) :=
    hasDusartSymmetricThetaBoundsBelow_of_endpoint_rows
      certificate.thetaCover
  have finiteShortInterval :
      HasLogCubedShortIntervalPrimeBelow (4e18 : Real) :=
    hasLogCubedShortIntervalPrimeBelow_of_rows certificate.logCover
  have thetaErrorAbove : HasThetaLogFourthErrorAbove A (599 : Real) :=
    hasThetaLogFourthErrorAbove_of_endpoint_rows_from_and_tail
      certificate.hA0 certificate.thetaErrorCover certificate.thetaTail
  exact completeClassification_of_split_theta_error_and_reserved_integral_core
    (by norm_num) (by norm_num) (by norm_num)
    finitePrimeCounting finiteTheta finiteShortInterval certificate.hA0
    certificate.hA1 (by norm_num) (by norm_num)
    small_integral_remainder_le_5990 (by norm_num) thetaErrorAbove
    (explicit_reserved_integral_core_at_599 (by norm_num)
      certificate.hA0 certificate.hA1)

/-! The same fixed-cutoff certificate with indexed finite families.  This is
the compact representation intended for large computational tables: the
kernel checks one finite index type and one coverage theorem per estimate. -/
structure Dusart599IndexedFiniteCertificate : Prop where
  primeCountingRows :
    ∃ n : Nat, ∃ rows : Fin n → DusartPrimeCountingEndpointRow,
      DusartPrimeCountingEndpointIndexedCoverFrom599 rows (4e18 : Real)
  thetaRows :
    ∃ n : Nat, ∃ rows : Fin n → DusartThetaEndpointRow,
      DusartThetaEndpointIndexedCoverUpTo rows (4e18 : Real)
  logRows :
    ∃ n : Nat, ∃ rows : Fin n → LogCubedPrimeRow,
      LogCubedPrimeIndexedCoverUpTo rows (4e18 : Real)
  thetaErrorRows :
    ∃ n : Nat, ∃ rows : Fin n → ThetaLogFourthEndpointRow (648 / 1000 : Real),
      ThetaLogFourthEndpointIndexedCoverFrom rows 599 (4e18 : Real)
  thetaTail : HasThetaLogFourthErrorAbove (648 / 1000 : Real) (4e18 : Real)

theorem Dusart599FiniteCertificate.toIndexed
    (certificate : Dusart599FiniteCertificate (648 / 1000 : Real)) :
    Dusart599IndexedFiniteCertificate := by
  refine {
    primeCountingRows := ⟨certificate.primeCountingRows.length,
      (fun i => certificate.primeCountingRows.get i),
      dusartPrimeCountingEndpointIndexedCover_of_list
        certificate.primeCountingCover⟩
    thetaRows := ⟨certificate.thetaRows.length,
      (fun i => certificate.thetaRows.get i),
      dusartThetaEndpointIndexedCover_of_list certificate.thetaCover⟩
    logRows := ⟨certificate.logRows.length,
      (fun i => certificate.logRows.get i),
      logCubedPrimeIndexedCover_of_list certificate.logCover⟩
    thetaErrorRows := ⟨certificate.thetaErrorRows.length,
      (fun i => certificate.thetaErrorRows.get i),
      thetaLogFourthEndpointIndexedCover_of_list certificate.thetaErrorCover⟩
    thetaTail := certificate.thetaTail }

theorem completeClassification_of_dusart_599_indexed_finite_certificate
    (certificate : Dusart599IndexedFiniteCertificate) :
    CompleteClassification := by
  obtain ⟨nPrime, primeRows, primeCover⟩ := certificate.primeCountingRows
  obtain ⟨nTheta, thetaRows, thetaCover⟩ := certificate.thetaRows
  obtain ⟨nLog, logRows, logCover⟩ := certificate.logRows
  obtain ⟨nError, errorRows, errorCover⟩ := certificate.thetaErrorRows
  have finitePrimeCounting :
    HasDusartRealPrimeCountingBoundsBelow (4e18 : Real) :=
    hasDusartRealPrimeCountingBoundsBelow_of_indexed_endpoint_rows
      primeCover
      dusartSmallUpperIntervalRows_provide
  have finiteTheta :
    HasDusartSymmetricThetaBoundsBelow (4e18 : Real) :=
    hasDusartSymmetricThetaBoundsBelow_of_indexed_endpoint_rows
      thetaCover
  have finiteShortInterval :
    HasLogCubedShortIntervalPrimeBelow (4e18 : Real) :=
    hasLogCubedShortIntervalPrimeBelow_of_indexed_rows
      logCover
  have thetaErrorAbove :
    HasThetaLogFourthErrorAbove (648 / 1000 : Real) (599 : Real) :=
    hasThetaLogFourthErrorAbove_of_indexed_endpoint_rows_from_and_tail
      (by norm_num) errorCover
      certificate.thetaTail
  exact completeClassification_of_split_theta_error_and_reserved_integral_core
    (by norm_num) (by norm_num) (by norm_num) finitePrimeCounting
    finiteTheta finiteShortInterval (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) small_integral_remainder_le_5990
    (by norm_num) thetaErrorAbove
    (explicit_reserved_integral_core_at_599 (by norm_num)
      (by norm_num) (by norm_num))

theorem completeClassification_of_full_record_finite_published_asymptotic_inputs
    (finitePrimeCounting : HasDusartRealPrimeCountingBoundsBelow (4e18 : Real))
    (finitePublished : HasDusartPublishedPrimeCountingBoundsBelow (4e9 : Real))
    (asymptotic : HasDusartPrimeCountingAsymptoticAbove (4e9 : Real))
    (finiteTheta : HasDusartSymmetricThetaBoundsBelow (4e18 : Real))
    {rows : List LogCubedPrimeRow}
    (cover : LogCubedPrimeRowsCoverUpTo rows (4e18 : Real))
    (thetaError : HasThetaLogCubedError (12167 / 500000 : Real) (4e18 : Real)) :
    CompleteClassification := by
  exact completeClassification_of_full_record_rows_and_finite_theta
    (hasDusartRealPrimeCountingBounds_of_finite_published_and_asymptotic
      finitePrimeCounting finitePublished asymptotic)
    finiteTheta cover thetaError

/-! The same assembly can consume the denominator-form estimates stated in
the Wang--Crapis paper directly.  The conversion to the comparison functions
used by the tail is proved in `ExplicitPrimeCounting`; it is not an
additional analytic hypothesis. -/
theorem completeClassification_of_full_record_published_prime_counting_inputs
    (finitePrimeCounting : HasDusartRealPrimeCountingBoundsBelow (4e18 : Real))
    (published : HasDusartPublishedPrimeCountingBounds)
    (finiteTheta : HasDusartSymmetricThetaBoundsBelow (4e18 : Real))
    {rows : List LogCubedPrimeRow}
    (cover : LogCubedPrimeRowsCoverUpTo rows (4e18 : Real))
    (thetaError : HasThetaLogCubedError (12167 / 500000 : Real) (4e18 : Real)) :
    CompleteClassification := by
  exact completeClassification_of_full_record_rows_and_finite_theta
    (hasDusartRealPrimeCountingBounds_of_below_and_above
      finitePrimeCounting
      (hasDusartRealPrimeCountingBoundsAbove_of_published published))
    finiteTheta cover thetaError

/-! Public assembly with the analytic inputs in the form used by the paper:
the finite prime-counting check is combined with the published tail estimate,
while the theta and short-interval estimates are supplied globally. -/
theorem completeClassification_of_published_analytic_inputs
    (finitePrimeCounting : HasDusartRealPrimeCountingBoundsBelow (4e18 : Real))
    (published : HasDusartPublishedPrimeCountingBounds)
    (thetaBounds : HasDusartSymmetricThetaBounds)
    (shortInterval : HasDusartShortIntervalPrime) :
    CompleteClassification := by
  exact completeClassification_of_full_record_short_interval_inputs
    (hasDusartRealPrimeCountingBounds_of_below_and_above
      finitePrimeCounting
      (hasDusartRealPrimeCountingBoundsAbove_of_published published))
    thetaBounds shortInterval

/-! The four inputs in the preceding theorem are exactly the explicit
analytic facts used by the published all-`k` argument.  Bundling them makes
the remaining provider obligation explicit at the public theorem boundary;
none of these fields is synthesized by a project axiom. -/
structure WangCrapisAnalyticInputs : Prop where
  finitePrimeCounting : HasDusartRealPrimeCountingBoundsBelow (4e18 : Real)
  publishedPrimeCounting : HasDusartPublishedPrimeCountingBounds
  thetaBounds : HasDusartSymmetricThetaBounds
  shortInterval : HasDusartShortIntervalPrime

theorem completeClassification_of_wangCrapis_analytic_inputs
    (inputs : WangCrapisAnalyticInputs) :
    CompleteClassification := by
  exact completeClassification_of_published_analytic_inputs
    inputs.finitePrimeCounting inputs.publishedPrimeCounting
    inputs.thetaBounds inputs.shortInterval

/-! The direct paper-facing boundary.  Wang--Crapis state the tail argument
using the prime-counting, Chebyshev-theta, and short-interval estimates
themselves.  This theorem keeps those three statements visible and uses only
the proved structural assembly below them. -/
structure WangCrapisPaperInputs : Prop where
  primeCounting : HasDusartPrimeCountingBounds
  thetaBounds : HasDusartThetaBounds
  shortInterval : HasDusartShortIntervalPrime

theorem completeClassification_of_wangCrapis_paper_inputs
    (inputs : WangCrapisPaperInputs) :
    CompleteClassification := by
  exact completeClassification_of_full_record_inputs
    inputs.primeCounting inputs.thetaBounds
    (hasUniformTailPrimePair_of_shortInterval inputs.shortInterval)

end

end PrimeFactorUnimodality
