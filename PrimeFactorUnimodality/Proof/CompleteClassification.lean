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
    (thetaError : HasThetaLogCubedError (12167 / 500000 : Real) (4e18 : Real))
    CompleteClassification := by
  exact completeClassification_of_full_record_bounded_rows
    primeCountingBounds thetaBounds (4e18 : Real) le_rfl cover thetaError

theorem completeClassification_of_full_record_rows_and_finite_theta
    (primeCountingBounds : HasDusartRealPrimeCountingBounds)
    (finiteTheta : HasDusartSymmetricThetaBoundsBelow (4e18 : Real))
    {rows : List LogCubedPrimeRow}
    (cover : LogCubedPrimeRowsCoverUpTo rows (4e18 : Real))
    (thetaError : HasThetaLogCubedError (12167 / 500000 : Real) (4e18 : Real))
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
    (thetaError : HasThetaLogCubedError (12167 / 500000 : Real) (4e18 : Real))
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

/-! A fully expanded core boundary: the opaque core inequality can be
replaced by the explicit logarithmic-integral inequality obtained from the
finite theta error. -/
theorem completeClassification_of_finite_theta_error_and_integral_core
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

theorem completeClassification_of_theta_error_rows_and_integral_core
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

theorem completeClassification_of_finite_theta_error_at_large_cutoff
    {A X : Real} (hX : (4e18 : Real) ≤ X)
    (finitePrimeCounting : HasDusartRealPrimeCountingBoundsBelow X)
    (finiteTheta : HasDusartSymmetricThetaBoundsBelow X)
    (finiteShortInterval : HasLogCubedShortIntervalPrimeBelow X)
    (hA0 : 0 ≤ A) (hA1 : A ≤ 1)
    (thetaErrorBelow : HasThetaLogFourthErrorBelow A X)
    (thetaErrorAbove : HasThetaLogFourthErrorAbove A X) :
    CompleteClassification := by
  have integralCoreBound :
      4000 + 720 * (∫ t in (2 : Real)..X, 1 / Real.log t ^ 7) +
          A * (∫ t in (2 : Real)..X, 1 / Real.log t ^ 6) ≤
        (3 / 5 : Real) * X / Real.log X ^ 4 := by
    have hexplicit := explicit_integral_core_bound_at_large_cutoff
      hX hA0 hA1
    have hmillionX : (1000000 : Real) ≤ X :=
      (by norm_num : (1000000 : Real) ≤ (4e18 : Real)).trans hX
    have hseven := integral_inv_log_seven_le_explicit hmillionX
    have hsix := integral_inv_log_six_le_explicit hmillionX
    have hA7 : 0 ≤ A := hA0
    have hseven_mul := mul_le_mul_of_nonneg_left hseven (by norm_num :
      (0 : Real) ≤ 720)
    have hsix_mul := mul_le_mul_of_nonneg_left hsix hA7
    nlinarith [hexplicit, hseven_mul, hsix_mul]
  exact completeClassification_of_finite_theta_error_and_integral_core
    hX finitePrimeCounting finiteTheta finiteShortInterval hA0 hA1
    (by norm_num) (by norm_num) thetaErrorBelow thetaErrorAbove
    integralCoreBound

/-! The source-level MediumPNT selects the cutoff; this wrapper makes the
remaining finite obligation explicit as a provider valid at every possible
selected cutoff.  Thus the resulting conclusion is the universal
classification, with no hidden fixed cutoff and no finite bound on `k`. -/
theorem completeClassification_of_mediumPNT_and_finite_provider
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
  obtain ⟨X, hX, h4X, thetaError⟩ :=
    exists_hasThetaLogFourthError_of_mediumPNT_above (4e18 : Real)
  exact completeClassification_of_finite_theta_error_at_large_cutoff
    h4X (finitePrimeCounting X h4X) (finiteTheta X h4X)
    (finiteShortInterval X h4X) (by norm_num) (by norm_num)
    (finiteThetaError X h4X)
    (fun x hx => thetaError x hx)

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
structure MediumPNTFiniteSplitRowProvider : Prop where
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

theorem completeClassification_of_mediumPNT_and_split_row_provider
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
structure MediumPNTFiniteIntegerSplitRowProvider : Prop where
  primeCountingRows : ∀ X : Real, (4e18 : Real) ≤ X →
    ∃ rows : List DusartPrimeCountingRow,
      DusartPrimeCountingRowsCoverFrom599 rows X
  primeCountingSmallIntegerRows : List DusartPrimeCountingUpperIntegerRow
  primeCountingSmallIntegerCover :
    DusartPrimeCountingUpperIntegerRowsCover
      primeCountingSmallIntegerRows
  thetaRows : ∀ X : Real, (4e18 : Real) ≤ X →
    ∃ rows : List DusartThetaBoundsRow,
      DusartThetaBoundsRowsCoverUpTo rows X
  shortIntervalRows : ∀ X : Real, (4e18 : Real) ≤ X →
    ∃ rows : List LogCubedPrimeRow,
      LogCubedPrimeRowsCoverUpTo rows X
  thetaErrorRows : ∀ X : Real, (4e18 : Real) ≤ X →
    ∃ rows : List (ThetaLogFourthErrorRow (648 / 1000 : Real)),
      ThetaLogFourthErrorRowsCoverUpTo rows X

theorem completeClassification_of_mediumPNT_and_integer_split_row_provider
    (provider : MediumPNTFiniteIntegerSplitRowProvider) :
    CompleteClassification := by
  refine completeClassification_of_mediumPNT_and_finite_error_provider
    (fun X hX => ?_) (fun X hX => ?_) (fun X hX => ?_) (fun X hX => ?_)
  · obtain ⟨rows, hcover⟩ := provider.primeCountingRows X hX
    exact hasDusartRealPrimeCountingBoundsBelow_of_rows_from599 hcover
      (real_primeCounting_upper_of_integer_rows
        provider.primeCountingSmallIntegerCover)
  · obtain ⟨rows, hcover⟩ := provider.thetaRows X hX
    exact hasDusartSymmetricThetaBoundsBelow_of_rows hcover
  · obtain ⟨rows, hcover⟩ := provider.shortIntervalRows X hX
    exact hasLogCubedShortIntervalPrimeBelow_of_rows hcover
  · obtain ⟨rows, hcover⟩ := provider.thetaErrorRows X hX
    exact hasThetaLogFourthErrorBelow_of_rows hcover

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
