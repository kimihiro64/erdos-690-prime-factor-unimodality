import PrimeFactorUnimodality.Proof.CompleteClassificationCore

set_option autoImplicit false

/-! # Complete classification provider assemblies

This module is a source-level split of the complete all-k classification assembly.
-/

namespace PrimeFactorUnimodality

noncomputable section

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

/-! Correct split-range adapter for the finite Dusart endpoint table.  The
published endpoint inequalities begin at the selected cutoff, while the
finite prefix supplies the theta estimate below that cutoff. -/
theorem mediumPNTSelectedFiniteInputs_of_split_lists
    {A X Y : Real}
    (hXY : X ≤ Y) (h4Y : (4e18 : Real) ≤ Y)
    {primeRows : List DusartPrimeCountingEndpointRow}
    (primeCover : DusartPrimeCountingEndpointRowsCoverFrom599 primeRows Y)
    {thetaRows : List DusartThetaEndpointRow}
    (thetaPrefix : HasDusartSymmetricThetaBoundsBelow (4e18 : Real))
    (thetaCover : DusartThetaEndpointRowsCoverFrom thetaRows (4e18 : Real) Y)
    {logRows : List LogCubedPrimeRow}
    (logCover : LogCubedPrimeRowsCoverUpTo logRows Y)
    (thetaError : HasThetaLogFourthError A Y) :
    MediumPNTSelectedFiniteInputs A X := by
  have finitePrimeCounting :
      HasDusartRealPrimeCountingBoundsBelow Y :=
    hasDusartRealPrimeCountingBoundsBelow_of_endpoint_rows
      primeCover dusartSmallUpperIntervalRows_provide
  have finiteTheta : HasDusartSymmetricThetaBoundsBelow Y :=
    hasDusartSymmetricThetaBoundsBelow_of_prefix_and_endpoint_rows
      (by norm_num) thetaPrefix thetaCover
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

end

end PrimeFactorUnimodality
