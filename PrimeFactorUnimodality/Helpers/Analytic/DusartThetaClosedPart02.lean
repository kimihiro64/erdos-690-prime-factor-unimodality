import PrimeFactorUnimodality.Helpers.Analytic.DusartThetaClosedPart01
import PrimeFactorUnimodality.Helpers.Analytic.DusartThetaClosedPart01Tail


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

theorem wangCrapis_thetaBounds_of_prefix_and_strict_rows_and_logFourthTail
    {A X x₀ : Real} (h2x₀ : (2 : Real) ≤ x₀)
    (hprefix : HasDusartSymmetricThetaBoundsBelow x₀)
    {n : Nat} (rows : Fin n → StrictThetaUpperRow)
    (cover : ∀ x : Real, x₀ ≤ x → x ≤ X →
      ∃ i : Fin n, (rows i).left ≤ x ∧ x ≤ (rows i).right)
    (lower : ∀ x : Real, 2 < x → x ≤ X →
      |Chebyshev.theta x - x| <
        (12323 / 10000 : Real) * x / Real.log x)
    (hXpos : 0 < X) (hlogX : (10 : Real) < Real.log X)
    (hA_nonneg : 0 ≤ A)
    (hA : A / Real.log X ≤ 12167 / 500000)
    (thetaError : HasThetaLogFourthError A X) :
    HasDusartThetaBounds := by
  exact wangCrapis_thetaBounds_of_logFourthTail hXpos hlogX
    (hasDusartSymmetricThetaBoundsBelow_of_prefix_and_indexed_strict_rows_and_lower
      h2x₀ hprefix cover lower)
    hA_nonneg hA thetaError

theorem wangCrapis_thetaBounds_of_six_prefix_and_endpoint_rows_and_logFourthTail
    {A X : Real} {n : Nat}
    (hXpos : 0 < X) (hlogX : (10 : Real) < Real.log X)
    (rows : Fin n → DusartThetaEndpointRow)
    (cover : DusartThetaEndpointIndexedCoverFrom rows (6 : Real) X)
    (margin : ∀ i, (rows i).theta_upper < (rows i).left)
    (lowerSuffix : ∀ x : Real, 6 ≤ x → x ≤ X →
      |Chebyshev.theta x - x| <
        (12323 / 10000 : Real) * x / Real.log x)
    (hA_nonneg : 0 ≤ A)
    (hA : A / Real.log X ≤ 12167 / 500000)
    (thetaError : HasThetaLogFourthError A X) :
    HasDusartThetaBounds := by
  let strictRows : Fin n → StrictThetaUpperRow :=
    fun i => (rows i).toStrictUpperRow (margin i)
  have strictCover : ∀ x : Real, (6 : Real) ≤ x → x ≤ X →
      ∃ i : Fin n, (strictRows i).left ≤ x ∧ x ≤ (strictRows i).right := by
    intro x hx hX
    obtain ⟨i, hleft, hright⟩ := cover x hx hX
    refine ⟨i, ?_, ?_⟩
    · simpa [strictRows, DusartThetaEndpointRow.toStrictUpperRow] using hleft
    · simpa [strictRows, DusartThetaEndpointRow.toStrictUpperRow] using hright
  apply wangCrapis_thetaBounds_of_prefix_and_strict_rows_and_logFourthTail
    (A := A) (x₀ := (6 : Real)) (by norm_num)
    wangCrapis_thetaBoundsBelow_6 strictRows strictCover ?_ hXpos hlogX
    hA_nonneg hA thetaError
  intro x hx hX
  by_cases hsmall : x ≤ 6
  · exact wangCrapis_theta_lower_error_below_six hx hsmall
  · exact lowerSuffix x (by linarith) hX

/-! The same assembler with the closed seven-endpoint prefix.  This lets a
    later finite row partition start after the prime `7`, while retaining the
    original six-endpoint interface above for existing callers. -/
theorem wangCrapis_thetaBounds_of_seven_prefix_and_endpoint_rows_and_logFourthTail
    {A X : Real} {n : Nat}
    (hXpos : 0 < X) (hlogX : (10 : Real) < Real.log X)
    (rows : Fin n → DusartThetaEndpointRow)
    (cover : DusartThetaEndpointIndexedCoverFrom rows (7 : Real) X)
    (margin : ∀ i, (rows i).theta_upper < (rows i).left)
    (lowerSuffix : ∀ x : Real, 7 ≤ x → x ≤ X →
      |Chebyshev.theta x - x| <
        (12323 / 10000 : Real) * x / Real.log x)
    (hA_nonneg : 0 ≤ A)
    (hA : A / Real.log X ≤ 12167 / 500000)
    (thetaError : HasThetaLogFourthError A X) :
    HasDusartThetaBounds := by
  let strictRows : Fin n → StrictThetaUpperRow :=
    fun i => (rows i).toStrictUpperRow (margin i)
  have strictCover : ∀ x : Real, (7 : Real) ≤ x → x ≤ X →
      ∃ i : Fin n, (strictRows i).left ≤ x ∧ x ≤ (strictRows i).right := by
    intro x hx hX
    obtain ⟨i, hleft, hright⟩ := cover x hx hX
    refine ⟨i, ?_, ?_⟩
    · simpa [strictRows, DusartThetaEndpointRow.toStrictUpperRow] using hleft
    · simpa [strictRows, DusartThetaEndpointRow.toStrictUpperRow] using hright
  apply wangCrapis_thetaBounds_of_prefix_and_strict_rows_and_logFourthTail
    (A := A) (x₀ := (7 : Real)) (by norm_num)
    wangCrapis_thetaBoundsBelow_7 strictRows strictCover ?_ hXpos hlogX
    hA_nonneg hA thetaError
  intro x hx hX
  by_cases hsmall : x ≤ 7
  · exact wangCrapis_theta_lower_error_below_seven hx hsmall
  · exact lowerSuffix x (by linarith) hX

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
  let strictRows : Fin n → StrictThetaUpperRow :=
    fun i => (rows i).toStrictUpperRow (margin i)
  have strictCover : ∀ x : Real, (3 : Real) ≤ x → x ≤ X →
      ∃ i : Fin n, (strictRows i).left ≤ x ∧ x ≤ (strictRows i).right := by
    intro x hx hX
    obtain ⟨i, hleft, hright⟩ := cover x hx hX
    refine ⟨i, ?_, ?_⟩
    · simpa [strictRows, DusartThetaEndpointRow.toStrictUpperRow] using hleft
    · simpa [strictRows, DusartThetaEndpointRow.toStrictUpperRow] using hright
  exact wangCrapis_thetaBounds_of_prefix_and_strict_rows_and_logFourthTail
    (A := A) (x₀ := (3 : Real)) (by norm_num)
    wangCrapis_thetaBoundsBelow_3 strictRows strictCover lower
    hXpos hlogX hA_nonneg hA thetaError

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

/-! A Table 6.6 chunk may be appended after an independently proved finite
    prefix.  This keeps the low endpoint computation separate from the
    coefficient-table computation while preserving one bounded cutoff. -/
theorem hasDusartSymmetricThetaBoundsBelow_of_prefix_and_table66_chunk
    {x₀ : Real} (h2x₀ : (2 : Real) ≤ x₀)
    (hprefix : HasDusartSymmetricThetaBoundsBelow x₀)
    (chunk : DusartThetaTable66Chunk) :
    HasDusartSymmetricThetaBoundsBelow chunk.cutoff := by
  apply hasDusartSymmetricThetaBoundsBelow_of_upper_lower
  · intro x hx hX
    by_cases hsmall : x ≤ x₀
    · exact hprefix.1 x (by linarith) hsmall
    · obtain ⟨i, hleft, hright⟩ := chunk.cover x
        (h2x₀.trans (le_of_not_ge hsmall)) hX
      exact (dusartThetaRelativeRow_to_bounds
        (chunk.toRelativeRows i)).upper x hleft hright
  · intro x hx hX
    by_cases hsmall : x ≤ x₀
    · exact hprefix.2 x hx hsmall
    · obtain ⟨i, hleft, hright⟩ := chunk.cover x
        (h2x₀.trans (le_of_not_ge hsmall)) hX
      exact (dusartThetaRelativeRow_to_bounds
        (chunk.toRelativeRows i)).lower x hx hleft hright

theorem wangCrapis_thetaBounds_of_prefix_and_table66_chunk_and_logFourthTail
    {A x₀ : Real} (h2x₀ : (2 : Real) ≤ x₀)
    (hprefix : HasDusartSymmetricThetaBoundsBelow x₀)
    (chunk : DusartThetaTable66Chunk)
    (hXpos : 0 < chunk.cutoff)
    (hlogX : (10 : Real) < Real.log chunk.cutoff)
    (hA_nonneg : 0 ≤ A)
    (hA : A / Real.log chunk.cutoff ≤ 12167 / 500000)
    (thetaError : HasThetaLogFourthError A chunk.cutoff) :
    HasDusartThetaBounds := by
  exact wangCrapis_thetaBounds_of_logFourthTail hXpos hlogX
    (hasDusartSymmetricThetaBoundsBelow_of_prefix_and_table66_chunk
      h2x₀ hprefix chunk)
    hA_nonneg hA thetaError

/-! The same prefix boundary accepts a compact list of Table 6.6 chunks.  The
append assembler is the only place where the chunks are joined, so the final
provider need not duplicate a theorem or a dispatch tree for each band. -/
theorem hasDusartSymmetricThetaBoundsBelow_of_prefix_and_table66_chunks
    {x₀ : Real} (h2x₀ : (2 : Real) ≤ x₀)
    (hprefix : HasDusartSymmetricThetaBoundsBelow x₀)
    (first : DusartThetaTable66Chunk)
    (rest : List DusartThetaTable66Chunk) :
    HasDusartSymmetricThetaBoundsBelow
      (DusartThetaTable66Chunk.appendMany first rest).cutoff := by
  exact hasDusartSymmetricThetaBoundsBelow_of_prefix_and_table66_chunk
    h2x₀ hprefix (DusartThetaTable66Chunk.appendMany first rest)

theorem wangCrapis_thetaBounds_of_prefix_and_table66_chunks_and_logFourthTail
    {A x₀ : Real} (h2x₀ : (2 : Real) ≤ x₀)
    (hprefix : HasDusartSymmetricThetaBoundsBelow x₀)
    (first : DusartThetaTable66Chunk)
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
    (hasDusartSymmetricThetaBoundsBelow_of_prefix_and_table66_chunks
      h2x₀ hprefix first rest)
    hA_nonneg hA thetaError

theorem wangCrapis_thetaBounds_of_prefix_and_table66_coefficient_data_and_logFourthTail
    {A x₀ X : Real} (h2x₀ : (2 : Real) ≤ x₀)
    (hprefix : HasDusartSymmetricThetaBoundsBelow x₀)
    (cover : ∀ x : Real, x₀ ≤ x → x ≤ X →
      ∃ data ∈ dusartThetaTable6_6CoefficientData,
        (data.left : Real) ≤ x ∧ x ≤ data.right)
    (lower : ∀ data ∈ dusartThetaTable6_6CoefficientData,
      ∀ x : Real, (data.left : Real) ≤ x → x ≤ data.right →
        data.a0 * x ≤ Chebyshev.theta x)
    (upper : ∀ data ∈ dusartThetaTable6_6CoefficientData,
      ∀ x : Real, (data.left : Real) ≤ x → x ≤ data.right →
        Chebyshev.theta x ≤ data.b0 * x)
    (hXpos : 0 < X) (hlogX : (10 : Real) < Real.log X)
    (hA_nonneg : 0 ≤ A)
    (hA : A / Real.log X ≤ 12167 / 500000)
    (thetaError : HasThetaLogFourthError A X) :
    HasDusartThetaBounds := by
  exact wangCrapis_thetaBounds_of_logFourthTail hXpos hlogX
    (hasDusartSymmetricThetaBoundsBelow_of_prefix_and_table66_coefficient_bounds
      h2x₀ hprefix cover lower upper)
    hA_nonneg hA thetaError

/-! The complete Table 6.6 formula interface can be attached to the same
    finite prefix.  The six inequalities are kept as separate inputs because
    they are the interval statements proved from the paper's explicit
    correction terms; the assembler then supplies the common relative-row
    bounds used by the tail theorem. -/
theorem wangCrapis_thetaBounds_of_prefix_and_table66_formula_data_and_logFourthTail
    {A x₀ X : Real} (h2x₀ : (2 : Real) ≤ x₀)
    (hprefix : HasDusartSymmetricThetaBoundsBelow x₀)
    (cover : ∀ x : Real, x₀ ≤ x → x ≤ X →
      ∃ data ∈ dusartThetaTable6_6CoefficientData,
        (data.left : Real) ≤ x ∧ x ≤ data.right)
    (lower_zero : ∀ data ∈ dusartThetaTable6_6CoefficientData,
      ∀ x : Real, (data.left : Real) ≤ x → x ≤ data.right →
        data.a0 * x ≤ Chebyshev.theta x)
    (upper_zero : ∀ data ∈ dusartThetaTable6_6CoefficientData,
      ∀ x : Real, (data.left : Real) ≤ x → x ≤ data.right →
        Chebyshev.theta x ≤ data.b0 * x)
    (lower_one : ∀ data ∈ dusartThetaTable6_6CoefficientData,
      ∀ x : Real, (data.left : Real) ≤ x → x ≤ data.right →
        x - data.a1 * x / Real.log x ≤ Chebyshev.theta x)
    (upper_one : ∀ data ∈ dusartThetaTable6_6CoefficientData,
      ∀ x : Real, (data.left : Real) ≤ x → x ≤ data.right →
        Chebyshev.theta x ≤ x + data.b1 * x / Real.log x)
    (lower_two : ∀ data ∈ dusartThetaTable6_6CoefficientData,
      ∀ x : Real, (data.left : Real) ≤ x → x ≤ data.right →
        x - data.a2 * x / Real.log x ^ 2 ≤ Chebyshev.theta x)
    (upper_two : ∀ data ∈ dusartThetaTable6_6CoefficientData,
      ∀ x : Real, (data.left : Real) ≤ x → x ≤ data.right →
        Chebyshev.theta x ≤ x + data.b2 * x / Real.log x ^ 2)
    (hXpos : 0 < X) (hlogX : (10 : Real) < Real.log X)
    (hA_nonneg : 0 ≤ A)
    (hA : A / Real.log X ≤ 12167 / 500000)
    (thetaError : HasThetaLogFourthError A X) :
    HasDusartThetaBounds := by
  have finite := hasDusartSymmetricThetaBoundsBelow_of_prefix_and_table66_coefficient_bounds
    h2x₀ hprefix cover lower_zero upper_zero
  exact wangCrapis_thetaBounds_of_logFourthTail hXpos hlogX finite
    hA_nonneg hA thetaError

/-! The same Table 6.6 boundary with all six inequalities bundled per row.
    A generated certificate can therefore provide one indexed/list proof
    object per interval without repeating the assembler's six dispatches. -/
theorem wangCrapis_thetaBounds_of_prefix_and_table66_formula_bounds_and_logFourthTail
    {A x₀ X : Real} (h2x₀ : (2 : Real) ≤ x₀)
    (hprefix : HasDusartSymmetricThetaBoundsBelow x₀)
    (cover : ∀ x : Real, x₀ ≤ x → x ≤ X →
      ∃ data ∈ dusartThetaTable6_6CoefficientData,
        (data.left : Real) ≤ x ∧ x ≤ data.right)
    (formula : ∀ data ∈ dusartThetaTable6_6CoefficientData,
      DusartThetaTable66FormulaBounds data)
    (hXpos : 0 < X) (hlogX : (10 : Real) < Real.log X)
    (hA_nonneg : 0 ≤ A)
    (hA : A / Real.log X ≤ 12167 / 500000)
    (thetaError : HasThetaLogFourthError A X) :
    HasDusartThetaBounds := by
  have finite := hasDusartSymmetricThetaBoundsBelow_of_prefix_and_table66_coefficient_bounds
    h2x₀ hprefix cover (fun data hdata => (formula data hdata).lower_zero)
    (fun data hdata => (formula data hdata).upper_zero)
  exact wangCrapis_thetaBounds_of_logFourthTail hXpos hlogX finite
    hA_nonneg hA thetaError

/-! The strict upper estimate has the same prefix/table split as the
    symmetric estimate.  Keeping this assembler adjacent to the bundled
    formula boundary makes the published strict prefix an explicit consumer
    of exactly the same Table 6.6 row proofs. -/
theorem hasStrictThetaUpperBelow_of_prefix_and_table66_formula_data
    {x₀ X : Real} (h2x₀ : (2 : Real) ≤ x₀)
    (hprefix : HasStrictThetaUpperBelow x₀)
    (cover : ∀ x : Real, x₀ ≤ x → x ≤ X →
      ∃ data ∈ dusartThetaTable6_6CoefficientData,
        (data.left : Real) ≤ x ∧ x ≤ data.right)
    (formula : ∀ data ∈ dusartThetaTable6_6CoefficientData,
      DusartThetaTable66FormulaBounds data) :
    HasStrictThetaUpperBelow X := by
  intro x hx hX
  by_cases hsmall : x ≤ x₀
  · exact hprefix x hx hsmall
  · obtain ⟨data, hdata, hleft, hright⟩ := cover x
      (le_of_not_ge hsmall) hX
    exact strictThetaUpper_of_table66_formula_data data hdata
      (formula data hdata) hleft hright

/-! The published row endpoints cover the real interval directly.  This
    specialization fixes the lower endpoint at the start of Table 6.6 and
    derives the cover from the checked natural endpoint list, leaving only
    the six row inequalities as data for the eventual finite proof. -/
theorem wangCrapis_thetaBounds_of_table66_formula_data_and_logFourthTail
    {A X : Real}
    (hprefix : HasDusartSymmetricThetaBoundsBelow (100000000 : Real))
    (hXcutoff : X ≤ (8e11 : Real))
    (lower_zero : ∀ data ∈ dusartThetaTable6_6CoefficientData,
      ∀ x : Real, (data.left : Real) ≤ x → x ≤ data.right →
        data.a0 * x ≤ Chebyshev.theta x)
    (upper_zero : ∀ data ∈ dusartThetaTable6_6CoefficientData,
      ∀ x : Real, (data.left : Real) ≤ x → x ≤ data.right →
        Chebyshev.theta x ≤ data.b0 * x)
    (lower_one : ∀ data ∈ dusartThetaTable6_6CoefficientData,
      ∀ x : Real, (data.left : Real) ≤ x → x ≤ data.right →
        x - data.a1 * x / Real.log x ≤ Chebyshev.theta x)
    (upper_one : ∀ data ∈ dusartThetaTable6_6CoefficientData,
      ∀ x : Real, (data.left : Real) ≤ x → x ≤ data.right →
        Chebyshev.theta x ≤ x + data.b1 * x / Real.log x)
    (lower_two : ∀ data ∈ dusartThetaTable6_6CoefficientData,
      ∀ x : Real, (data.left : Real) ≤ x → x ≤ data.right →
        x - data.a2 * x / Real.log x ^ 2 ≤ Chebyshev.theta x)
    (upper_two : ∀ data ∈ dusartThetaTable6_6CoefficientData,
      ∀ x : Real, (data.left : Real) ≤ x → x ≤ data.right →
        Chebyshev.theta x ≤ x + data.b2 * x / Real.log x ^ 2)
    (hXpos : 0 < X) (hlogX : (10 : Real) < Real.log X)
    (hA_nonneg : 0 ≤ A)
    (hA : A / Real.log X ≤ 12167 / 500000)
    (thetaError : HasThetaLogFourthError A X) :
    HasDusartThetaBounds := by
  apply wangCrapis_thetaBounds_of_prefix_and_table66_formula_data_and_logFourthTail
    (x₀ := (100000000 : Real)) (X := X) (by norm_num) hprefix
    (fun x hx hupper => dusartThetaTable6_6CoefficientData_cover_real x hx
      (hupper.trans hXcutoff))
    lower_zero upper_zero lower_one upper_one lower_two upper_two
    hXpos hlogX hA_nonneg hA thetaError

theorem wangCrapis_thetaBounds_of_table66_formula_bounds_and_logFourthTail
    {A X : Real}
    (hprefix : HasDusartSymmetricThetaBoundsBelow (100000000 : Real))
    (hXcutoff : X ≤ (8e11 : Real))
    (formula : ∀ data ∈ dusartThetaTable6_6CoefficientData,
      DusartThetaTable66FormulaBounds data)
    (hXpos : 0 < X) (hlogX : (10 : Real) < Real.log X)
    (hA_nonneg : 0 ≤ A)
    (hA : A / Real.log X ≤ 12167 / 500000)
    (thetaError : HasThetaLogFourthError A X) :
    HasDusartThetaBounds := by
  apply wangCrapis_thetaBounds_of_prefix_and_table66_formula_bounds_and_logFourthTail
    (x₀ := (100000000 : Real)) (X := X) (by norm_num) hprefix
    (fun x hx hupper => dusartThetaTable6_6CoefficientData_cover_real x hx
      (hupper.trans hXcutoff))
    formula hXpos hlogX hA_nonneg hA thetaError

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
