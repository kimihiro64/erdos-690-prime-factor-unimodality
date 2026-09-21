import PrimeFactorUnimodality.Proof.CompleteClassificationProviders

set_option autoImplicit false

/-! # Complete classification integer-interval providers

This module is a source-level split of the complete all-k classification assembly.
-/

namespace PrimeFactorUnimodality

noncomputable section

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

/-! The same bundled boundary can be supplied as one ordinary list.  This is
the representation used by certificate generators: the four projections are
covered by the same ordered blocks, so no independent 10k-row duplication is
needed at the provider boundary. -/
structure MediumPNTFiniteIntegerIntervalPrefixBundleListCover
    (rows : List MediumPNTFiniteIntegerIntervalPrefixBundle) (X : Real) : Prop where
  primeCounting : DusartPrimeCountingEndpointRowsCoverFrom599
    (rows.map (fun row => row.primeCounting)) X
  theta : DusartThetaEndpointRowsCoverUpTo
    (rows.map (fun row => row.theta)) X
  shortInterval : LogCubedPrimeRowsCoverUpTo
    (rows.map (fun row => row.shortInterval)) X
  thetaError : ThetaLogFourthEndpointRowsCoverFrom
    (rows.map (fun row => row.thetaError)) (4e18 : Real) X

theorem mediumPNTFiniteIntegerIntervalPrefixBundleCover_of_list
    {rows : List MediumPNTFiniteIntegerIntervalPrefixBundle} {X : Real}
    (cover : MediumPNTFiniteIntegerIntervalPrefixBundleListCover rows X) :
    MediumPNTFiniteIntegerIntervalPrefixBundleCover
      (fun i : Fin rows.length => rows.get i) X := by
  constructor
  · simpa using
      (dusartPrimeCountingEndpointIndexedCover_of_list cover.primeCounting)
  · simpa using
      (dusartThetaEndpointIndexedCover_of_list cover.theta)
  · simpa using
      (logCubedPrimeIndexedCover_of_list cover.shortInterval)
  · simpa [ThetaLogFourthEndpointIndexedCoverUpTo] using
      (thetaLogFourthEndpointIndexedCover_of_list
        (x₀ := (4e18 : Real)) cover.thetaError)

theorem mediumPNTFiniteIntegerIntervalPrefixBundleListCover_append
    {m X : Real}
    {left right : List MediumPNTFiniteIntegerIntervalPrefixBundle}
    (hm : (4e18 : Real) ≤ m)
    (hleft : MediumPNTFiniteIntegerIntervalPrefixBundleListCover left m)
    (hright : MediumPNTFiniteIntegerIntervalPrefixBundleListCover right X) :
    MediumPNTFiniteIntegerIntervalPrefixBundleListCover (left ++ right) X := by
  constructor
  · simpa [List.map_append] using
      (dusartPrimeCountingEndpointRowsCoverFrom599_append
        hleft.primeCounting hright.primeCounting)
  · simpa [List.map_append] using
      (dusartThetaEndpointRowsCoverUpTo_append
        hleft.theta hright.theta)
  · simpa [List.map_append] using
      (logCubedPrimeRowsCoverUpTo_append
        hleft.shortInterval hright.shortInterval)
  · have hrightFrom : ThetaLogFourthEndpointRowsCoverFrom
        (right.map (fun row => row.thetaError)) m X := by
      intro x hx hX
      exact hright.thetaError x (hm.trans hx) hX
    simpa [List.map_append] using
      (thetaLogFourthEndpointRowsCoverFrom_append
        hleft.thetaError hrightFrom)

theorem mediumPNTFiniteIntegerIntervalPrefixBundleCover_append
    {m X : Real} {n₁ n₂ : Nat}
    {left : Fin n₁ → MediumPNTFiniteIntegerIntervalPrefixBundle}
    {right : Fin n₂ → MediumPNTFiniteIntegerIntervalPrefixBundle}
    (hleft : MediumPNTFiniteIntegerIntervalPrefixBundleCover left m)
    (hright : MediumPNTFiniteIntegerIntervalPrefixBundleCover right X) :
    MediumPNTFiniteIntegerIntervalPrefixBundleCover (Fin.append left right) X := by
  constructor
  · simpa [Fin.append_left, Fin.append_right] using
      (dusartPrimeCountingEndpointIndexedCoverFrom599_append
        hleft.primeCounting hright.primeCounting)
  · simpa [Fin.append_left, Fin.append_right] using
      (dusartThetaEndpointIndexedCoverUpTo_append
        hleft.theta hright.theta)
  · simpa [Fin.append_left, Fin.append_right] using
      (logCubedPrimeIndexedCoverUpTo_append
        hleft.shortInterval hright.shortInterval)
  · simpa [Fin.append_left, Fin.append_right] using
      (thetaLogFourthEndpointIndexedCoverFrom_append
        hleft.thetaError hright.thetaError)

structure MediumPNTFiniteIntegerIntervalBundledPrefixProvider : Prop where
  rows : Nat → MediumPNTFiniteIntegerIntervalPrefixBundle
  prefix : ∀ X : Real, (4e18 : Real) ≤ X →
    ∃ n : Nat,
      MediumPNTFiniteIntegerIntervalPrefixBundleCover
        (fun i : Fin n => rows i) X

/-! A generator may instead emit the finite prefix as one list, while still
using one fixed global row family.  `List.ofFn` makes that representation
definitionally compatible with the indexed provider after the cover lemma. -/
structure MediumPNTFiniteIntegerIntervalBundledListPrefixProvider : Prop where
  rows : Nat → MediumPNTFiniteIntegerIntervalPrefixBundle
  prefix : ∀ X : Real, (4e18 : Real) ≤ X →
    ∃ n : Nat,
      MediumPNTFiniteIntegerIntervalPrefixBundleListCover
        (List.ofFn (fun i : Fin n => rows i)) X

theorem MediumPNTFiniteIntegerIntervalBundledListPrefixProvider.toIndexed
    (provider : MediumPNTFiniteIntegerIntervalBundledListPrefixProvider) :
    MediumPNTFiniteIntegerIntervalBundledPrefixProvider := by
  refine { rows := provider.rows, prefix := ?_ }
  intro X hX
  obtain ⟨n, hcover⟩ := provider.prefix X hX
  refine ⟨n, (fun i : Fin n => provider.rows i), ?_⟩
  simpa using (mediumPNTFiniteIntegerIntervalPrefixBundleCover_of_list hcover)

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

theorem completeClassification_of_mediumPNT_and_integer_interval_bundled_list_prefix_provider
    (provider : MediumPNTFiniteIntegerIntervalBundledListPrefixProvider) :
    CompleteClassification := by
  exact completeClassification_of_mediumPNT_and_integer_interval_bundled_prefix_provider
    provider.toIndexed

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

end

end PrimeFactorUnimodality
