import Mathlib.NumberTheory.Primorial
import PrimeFactorUnimodality.Helpers.Analytic.ExplicitPrimeCounting
import PrimeFactorUnimodality.Helpers.Analytic.PrimeWeightSum
import PrimeFactorUnimodality.Helpers.PrimeSequence.AverageGap
import PrimeFactorUnimodality.Helpers.PrimeSequence.CRTCompositeBlock
import PrimeFactorUnimodality.Helpers.Unimodality.Certificate

set_option autoImplicit false

/-! # Structural uniform-tail valley construction -/

namespace PrimeFactorUnimodality

noncomputable section

/-- The symmetric CRT descent and a later average-gap ascent obstruct
unimodality.  All analytic work is isolated in prime-count and ratio
hypotheses that do not mention the CRT shift chosen by the proof. -/
theorem uniformConstruction_not_isUnimodal
    {qPrev q k bound : Nat}
    (consecutive : ConsecutivePrimes qPrev q)
    (qPrev_gt_two : 2 < qPrev)
    (hk : 2 ≤ k)
    (two_le_count :
      2 ≤ Nat.primeCounting (9 * primorial q) -
        Nat.primeCounting (4 * primorial q))
    (interval_short :
      9 * primorial q - 4 * primorial q <
        (Nat.primeCounting (9 * primorial q) -
          Nat.primeCounting (4 * primorial q) - 1) * bound)
    (descentDefined :
      k - 1 ≤ Nat.primeCounting' (2 * primorial q + 1) - 1)
    (descentRatio : ∀ a < primorial q,
      densityRatio
          (primesBelow
            (primeAt (Nat.primeCounting' (a + 2 * primorial q + 1) - 1)))
          (k - 1) < 2 * qPrev + 1)
    (ascentRatio :
      ∀ i < Nat.primeCounting (9 * primorial q) -
          Nat.primeCounting (4 * primorial q) - 1,
        (bound : Rat) <
          densityRatio
            (primesBelow
              (primeAt (Nat.primeCounting (4 * primorial q) + i)))
            (k - 1)) :
    ¬ IsUnimodal (primeFactorDensity k) := by
  let P := primorial q
  have P_eq : P = ∏ p ∈ Nat.primesLE q, p := by
    exact primorial_eq_prod_primesLE q
  obtain ⟨a, ha, descentGap, _descentPredecessor⟩ :=
    exists_large_primeGap_with_predecessor_of_consecutive consecutive qPrev_gt_two
  rw [← P_eq] at ha descentGap _descentPredecessor
  obtain ⟨i, hi, ascentGap⟩ := exists_primeGap_lt_of_count
    (4 * P) (9 * P) bound (by simpa only [P] using two_le_count)
      (by simpa only [P] using interval_short)
  let descentIndex := Nat.primeCounting' (a + 2 * P + 1) - 1
  let ascentIndex := Nat.primeCounting (4 * P) + i
  have P_pos : 0 < P := primorial_pos q
  have descentCutoff_gt_two : 2 < a + 2 * P + 1 := by omega
  have descentBeforeAscent : descentIndex < ascentIndex := by
    have descentPrime_lt : primeAt descentIndex < a + 2 * P + 1 := by
      exact primeAt_primeCounting'_sub_one_lt descentCutoff_gt_two
    have cutoff_lt_lower : a + 2 * P + 1 < 4 * P := by omega
    have lower_le_startPrime :
        4 * P ≤ primeAt (Nat.primeCounting (4 * P)) := by
      dsimp only [Nat.primeCounting]
      exact (by omega : 4 * P ≤ 4 * P + 1).trans
        (Nat.le_nth_count Nat.infinite_setOfPred_prime (4 * P + 1))
    have startPrime_le_ascent :
        primeAt (Nat.primeCounting (4 * P)) ≤ primeAt ascentIndex := by
      apply primeAt_strictMono.monotone
      dsimp only [ascentIndex]
      omega
    have prime_lt : primeAt descentIndex < primeAt ascentIndex :=
      descentPrime_lt.trans (cutoff_lt_lower.trans_le
        (lower_le_startPrime.trans startPrime_le_ascent))
    by_contra not_lt
    have reverse := primeAt_strictMono.monotone (Nat.le_of_not_gt not_lt)
    omega
  have ratioDefinedAtDescent : k - 1 ≤ descentIndex := by
    have descentDefinedP :
        k - 1 ≤ Nat.primeCounting' (2 * P + 1) - 1 := by
      simpa only [P] using descentDefined
    have countMono := Nat.monotone_primeCounting'
      (show 2 * P + 1 ≤ a + 2 * P + 1 by omega)
    dsimp only [descentIndex]
    omega
  have ratioDefinedAtAscent : k - 1 ≤ ascentIndex := by
    have countMono :
        Nat.primeCounting' (2 * P + 1) ≤ Nat.primeCounting (4 * P) := by
      dsimp only [Nat.primeCounting]
      apply Nat.monotone_primeCounting'
      omega
    dsimp only [ascentIndex]
    omega
  let certificate : RatioValleyCertificate (k - 2) :=
    { descentIndex := descentIndex
      ascentIndex := ascentIndex
      ratioDefinedAtDescent := by
        simpa [show k - 2 + 1 = k - 1 by omega] using ratioDefinedAtDescent
      ratioDefinedAtAscent := by
        simpa [show k - 2 + 1 = k - 1 by omega] using ratioDefinedAtAscent
      descentBeforeAscent := descentBeforeAscent
      descentRatio := by
        have descentGapIndex : 2 * qPrev ≤ primeGap descentIndex := by
          simpa only [descentIndex] using descentGap
        have thresholdLe : ((2 * qPrev + 1 : Nat) : Rat) ≤
            (primeGap descentIndex + 1 : Nat) := by
          exact_mod_cast (show 2 * qPrev + 1 ≤ primeGap descentIndex + 1 by omega)
        have thresholdLeAtA : (2 : Rat) * qPrev + 1 ≤
            (primeGap
                (Nat.primeCounting' (a + 2 * primorial q + 1) - 1) + 1 : Nat) := by
          simpa only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one,
            descentIndex, P] using thresholdLe
        simpa only [show k - 2 + 1 = k - 1 by omega, descentIndex, P] using
          (descentRatio a (by simpa only [P] using ha)).trans_le thresholdLeAtA
      ascentRatio := by
        have ascentGapIndex : primeGap ascentIndex < bound := by
          simpa only [ascentIndex] using ascentGap
        have gapLe : ((primeGap ascentIndex + 1 : Nat) : Rat) ≤ bound := by
          exact_mod_cast (show primeGap ascentIndex + 1 ≤ bound by omega)
        simpa only [show k - 2 + 1 = k - 1 by omega, ascentIndex, P] using
          gapLe.trans_lt (ascentRatio i (by simpa only [P] using hi)) }
  simpa [show k - 2 + 2 = k by omega] using certificate.not_isUnimodal

/-! The structural valley theorem also has a provider-free boundary.  This
form is the interface used by the elementary Chebyshev tail: its only
prime-counting inputs are the two concrete shell inequalities themselves. -/
theorem uniformConstruction_not_isUnimodal_of_explicit_shell_count
    {qPrev q k bound : Nat}
    (consecutive : ConsecutivePrimes qPrev q)
    (qPrev_gt_two : 2 < qPrev)
    (hk : 2 ≤ k)
    (two_le_count :
      2 ≤ Nat.primeCounting (9 * primorial q) -
        Nat.primeCounting (4 * primorial q))
    (interval_short :
      9 * primorial q - 4 * primorial q <
        (Nat.primeCounting (9 * primorial q) -
          Nat.primeCounting (4 * primorial q) - 1) * bound)
    (descentDefined :
      k - 1 ≤ Nat.primeCounting' (2 * primorial q + 1) - 1)
    (descentRatio : ∀ a < primorial q,
      densityRatio
          (primesBelow
            (primeAt (Nat.primeCounting' (a + 2 * primorial q + 1) - 1)))
          (k - 1) < 2 * qPrev + 1)
    (ascentRatio :
      ∀ i < Nat.primeCounting (9 * primorial q) -
          Nat.primeCounting (4 * primorial q) - 1,
        (bound : Rat) <
          densityRatio
            (primesBelow
              (primeAt (Nat.primeCounting (4 * primorial q) + i)))
            (k - 1)) :
    ¬ IsUnimodal (primeFactorDensity k) := by
  exact uniformConstruction_not_isUnimodal consecutive qPrev_gt_two hk
    two_le_count interval_short descentDefined descentRatio ascentRatio

/-- Discharge the two prime-count hypotheses of
`uniformConstruction_not_isUnimodal` from Dusart's explicit bounds and two
purely numerical inequalities. -/
theorem uniformConstruction_not_isUnimodal_of_dusart_count
    {qPrev q k bound target : Nat}
    (primeCountingBounds : HasDusartPrimeCountingBounds)
    (consecutive : ConsecutivePrimes qPrev q)
    (qPrev_gt_two : 2 < qPrev)
    (hk : 2 ≤ k)
    (primorial_large : 599 ≤ 9 * primorial q)
    (target_pos : 1 ≤ target)
    (shellNumeric :
      (target : Real) <
        dusartPiLower (9 * primorial q) -
          dusartPiUpper (4 * primorial q))
    (widthNumeric : 5 * primorial q < target * bound)
    (descentDefined :
      k - 1 ≤ Nat.primeCounting' (2 * primorial q + 1) - 1)
    (descentRatio : ∀ a < primorial q,
      densityRatio
          (primesBelow
            (primeAt (Nat.primeCounting' (a + 2 * primorial q + 1) - 1)))
          (k - 1) < 2 * qPrev + 1)
    (ascentRatio :
      ∀ i < Nat.primeCounting (9 * primorial q) -
          Nat.primeCounting (4 * primorial q) - 1,
        (bound : Rat) <
          densityRatio
            (primesBelow
              (primeAt (Nat.primeCounting (4 * primorial q) + i)))
            (k - 1)) :
    ¬ IsUnimodal (primeFactorDensity k) := by
  have P_pos : 0 < primorial q := primorial_pos q
  have shellCount :
      target + 1 ≤ Nat.primeCounting (9 * primorial q) -
        Nat.primeCounting (4 * primorial q) := by
    apply nat_le_primeCounting_sub_of_lt_dusart primeCountingBounds
      (show 2 ≤ 4 * primorial q by omega)
      primorial_large
      (by omega)
    simpa only [Nat.cast_mul, Nat.cast_ofNat] using shellNumeric
  apply uniformConstruction_not_isUnimodal consecutive qPrev_gt_two hk
  · omega
  · have widthEq : 9 * primorial q - 4 * primorial q = 5 * primorial q := by
      omega
    rw [widthEq]
    exact interval_short_of_count_lower shellCount widthNumeric
  · exact descentDefined
  · exact descentRatio
  · exact ascentRatio

/-- Direct average-gap form of the Dusart reduction.  The numerical premise
compares the shell count with `width / bound + 1`, which is usually much easier
to establish when `bound` itself depends on the selected prime. -/
theorem uniformConstruction_not_isUnimodal_of_dusart_count_direct
    {qPrev q k bound : Nat}
    (primeCountingBounds : HasDusartPrimeCountingBounds)
    (consecutive : ConsecutivePrimes qPrev q)
    (qPrev_gt_two : 2 < qPrev)
    (hk : 2 ≤ k)
    (bound_pos : 1 ≤ bound)
    (primorial_large : 599 ≤ 9 * primorial q)
    (shellNumeric :
      ((5 * primorial q : Nat) : Real) / bound + 1 <
        dusartPiLower (9 * primorial q) -
          dusartPiUpper (4 * primorial q))
    (descentDefined :
      k - 1 ≤ Nat.primeCounting' (2 * primorial q + 1) - 1)
    (descentRatio : ∀ a < primorial q,
      densityRatio
          (primesBelow
            (primeAt (Nat.primeCounting' (a + 2 * primorial q + 1) - 1)))
          (k - 1) < 2 * qPrev + 1)
    (ascentRatio :
      ∀ i < Nat.primeCounting (9 * primorial q) -
          Nat.primeCounting (4 * primorial q) - 1,
        (bound : Rat) <
          densityRatio
            (primesBelow
              (primeAt (Nat.primeCounting (4 * primorial q) + i)))
            (k - 1)) :
    ¬ IsUnimodal (primeFactorDensity k) := by
  have P_pos : 0 < primorial q := primorial_pos q
  obtain ⟨twoCount, short⟩ := count_and_width_of_dusart
    (x := 4 * primorial q) (y := 9 * primorial q)
      (width := 5 * primorial q) (bound := bound)
      primeCountingBounds (show 2 ≤ 4 * primorial q by omega)
      primorial_large (by omega) bound_pos (by
        simpa only [Nat.cast_mul, Nat.cast_ofNat] using shellNumeric)
  apply uniformConstruction_not_isUnimodal (bound := bound)
    consecutive qPrev_gt_two hk
    twoCount
  · have widthEq : 9 * primorial q - 4 * primorial q =
        5 * primorial q := by omega
    rwa [widthEq]
  · exact descentDefined
  · exact descentRatio
  · exact ascentRatio

/-- Discharge all density-ratio hypotheses of the uniform construction from
two bounds on the canonical prime-weight summatory function.  The descent
uses only the primes through the primorial `P`; the ascent uses the harmless
upper frontier `8P`. -/
theorem uniformConstruction_not_isUnimodal_of_weight_bounds
    {qPrev q k bound target : Nat}
    (primeCountingBounds : HasDusartPrimeCountingBounds)
    (consecutive : ConsecutivePrimes qPrev q)
    (qPrev_gt_two : 2 < qPrev)
    (hk : 2 ≤ k)
    (bound_pos : 1 ≤ bound)
    (primorial_large : 599 ≤ 9 * primorial q)
    (target_pos : 1 ≤ target)
    (shellNumeric :
      (target : Real) <
        dusartPiLower (9 * primorial q) -
          dusartPiUpper (4 * primorial q))
    (widthNumeric : 5 * primorial q < target * bound)
    (descentDefined :
      k - 1 ≤ Nat.primeCounting' (2 * primorial q + 1) - 1)
    (descentWeight :
      ((k - 1 : Nat) : Real) < ((2 * qPrev + 1 : Nat) : Real) *
        (primeWeightSumBelow (primorial q + 1) -
          primeWeightSumBelow (primeAt (k - 2))))
    (ascentWeight :
      (bound : Real) * primeWeightSumBelow (9 * primorial q + 1) <
        ((k - 1 : Nat) : Real)) :
    ¬ IsUnimodal (primeFactorDensity k) := by
  let P := primorial q
  have P_pos : 0 < P := primorial_pos q
  apply uniformConstruction_not_isUnimodal_of_dusart_count
    primeCountingBounds consecutive qPrev_gt_two hk primorial_large target_pos
    shellNumeric widthNumeric descentDefined
  · intro a ha
    let index := Nat.primeCounting' (a + 2 * P + 1) - 1
    have predecessor_gt : P < primeAt index := by
      exact primeAt_primeCounting_sub_one_gt_of_two_mul_lt P_pos (by omega)
    have indexDefined : k - 1 ≤ index := by
      have countMono := Nat.monotone_primeCounting'
        (show 2 * P + 1 ≤ a + 2 * P + 1 by omega)
      dsimp only [index]
      have definedP : k - 1 ≤ Nat.primeCounting' (2 * P + 1) - 1 := by
        simpa only [P] using descentDefined
      omega
    have leadingEq :
        realLeadingWeightSum (primesBelow (primeAt index)) (k - 2) =
          primeWeightSumBelow (primeAt (k - 2)) := by
      exact realLeadingWeightSum_primesBelow_primeAt _ _ (by omega)
    have fullLower :
        primeWeightSumBelow (P + 1) ≤
          realWeightSum (primesBelow (primeAt index)) := by
      change primeWeightSumBelow (P + 1) ≤
        primeWeightSumBelow (primeAt index)
      exact primeWeightSumBelow_mono (by omega)
    have shellPositive :
        0 < primeWeightSumBelow (P + 1) -
          primeWeightSumBelow (primeAt (k - 2)) := by
      have factorPositive : (0 : Real) < ((2 * qPrev + 1 : Nat) : Real) := by
        positivity
      have productPositive := (show (0 : Real) < ((k - 1 : Nat) : Real) by
        exact_mod_cast (show 0 < k - 1 by omega)).trans descentWeight
      exact (mul_pos_iff.mp productPositive).resolve_right
        (fun h ↦ (not_lt_of_ge (le_of_lt factorPositive)) h.1) |>.2
    have complementPositive :
        0 < realWeightSum (primesBelow (primeAt index)) -
          realLeadingWeightSum (primesBelow (primeAt index)) (k - 2) := by
      rw [leadingEq]
      linarith
    have ratioLe := real_densityRatio_le_degree_div_weightSum_sub_leading
      (primesBelow (primeAt index)) (primesBelow_gt_one _)
      (primesBelow_weights_descending _) (k - 1) (by omega)
      (by simpa [primesBelow_primeAt_length] using indexDefined)
      (by
        have complementPositive' := complementPositive
        rw [← ratCast_weightSum, ← ratCast_leadingWeightSum] at complementPositive'
        have ratPositive :
            0 < weightSum (primesBelow (primeAt index)) -
              leadingWeightSum (primesBelow (primeAt index)) (k - 2) := by
          exact_mod_cast complementPositive'
        simpa only [show k - 1 - 1 = k - 2 by omega] using ratPositive)
    have castRatioLt :
        (densityRatio (primesBelow (primeAt index)) (k - 1) : Real) <
          ((2 * qPrev + 1 : Nat) : Real) := by
      rw [show k - 1 - 1 = k - 2 by omega] at ratioLe
      refine ratioLe.trans_lt ((div_lt_iff₀ complementPositive).2 ?_)
      rw [leadingEq]
      have thresholdNonneg : (0 : Real) ≤ ((2 * qPrev + 1 : Nat) : Real) := by
        positivity
      nlinarith [mul_le_mul_of_nonneg_left fullLower thresholdNonneg,
        descentWeight]
    exact_mod_cast castRatioLt
  · intro i hi
    let index := Nat.primeCounting (4 * P) + i
    have indexDefined : k - 1 ≤ index := by
      have countMono :
          Nat.primeCounting' (2 * P + 1) ≤ Nat.primeCounting (4 * P) := by
        dsimp only [Nat.primeCounting]
        apply Nat.monotone_primeCounting'
        omega
      dsimp only [index]
      have definedP : k - 1 ≤ Nat.primeCounting' (2 * P + 1) - 1 := by
        simpa only [P] using descentDefined
      omega
    have primeUpper : primeAt index ≤ 9 * P := by
      apply primeAt_primeCounting_add_le_upper
      have hiP :
          i < Nat.primeCounting (9 * P) - Nat.primeCounting (4 * P) - 1 := by
        simpa only [P] using hi
      omega
    have fullUpper :
        realWeightSum (primesBelow (primeAt index)) ≤
          primeWeightSumBelow (9 * P + 1) := by
      change primeWeightSumBelow (primeAt index) ≤
        primeWeightSumBelow (9 * P + 1)
      exact primeWeightSumBelow_mono (by omega)
    have entriesNonempty : primesBelow (primeAt index) ≠ [] := by
      intro empty
      have lengthZero : (primesBelow (primeAt index)).length = 0 := by simp [empty]
      rw [primesBelow_primeAt_length] at lengthZero
      omega
    have sumPositiveRat : 0 < weightSum (primesBelow (primeAt index)) :=
      weightSum_pos_of_ne_nil _ (primesBelow_gt_one _) entriesNonempty
    have sumPositive : 0 < realWeightSum (primesBelow (primeAt index)) := by
      rw [← ratCast_weightSum]
      exact_mod_cast sumPositiveRat
    have ratioLower := real_degree_div_weightSum_le_densityRatio
      (primesBelow (primeAt index)) (primesBelow_gt_one _) (k - 1)
      (by simpa [primesBelow_primeAt_length] using indexDefined) sumPositiveRat
    have boundNonneg : (0 : Real) ≤ (bound : Real) := by positivity
    have productUpper :
        (bound : Real) * realWeightSum (primesBelow (primeAt index)) <
          ((k - 1 : Nat) : Real) := by
      exact (mul_le_mul_of_nonneg_left fullUpper boundNonneg).trans_lt
        (by simpa only [P] using ascentWeight)
    have castRatioGt :
        (bound : Real) <
          (densityRatio (primesBelow (primeAt index)) (k - 1) : Real) := by
      exact ((lt_div_iff₀ sumPositive).2 productUpper).trans_le ratioLower
    exact_mod_cast castRatioGt

/-- Direct-shell counterpart of
`uniformConstruction_not_isUnimodal_of_weight_bounds`. -/
theorem uniformConstruction_not_isUnimodal_of_weight_bounds_direct
    {qPrev q k bound : Nat}
    (primeCountingBounds : HasDusartPrimeCountingBounds)
    (consecutive : ConsecutivePrimes qPrev q)
    (qPrev_gt_two : 2 < qPrev)
    (hk : 2 ≤ k)
    (bound_pos : 1 ≤ bound)
    (primorial_large : 599 ≤ 9 * primorial q)
    (shellNumeric :
      ((5 * primorial q : Nat) : Real) / bound + 1 <
        dusartPiLower (9 * primorial q) -
          dusartPiUpper (4 * primorial q))
    (descentDefined :
      k - 1 ≤ Nat.primeCounting' (2 * primorial q + 1) - 1)
    (descentWeight :
      ((k - 1 : Nat) : Real) < ((2 * qPrev + 1 : Nat) : Real) *
        (primeWeightSumBelow (primorial q + 1) -
          primeWeightSumBelow (primeAt (k - 2))))
    (ascentWeight :
      (bound : Real) * primeWeightSumBelow (9 * primorial q + 1) <
        ((k - 1 : Nat) : Real)) :
    ¬ IsUnimodal (primeFactorDensity k) := by
  let P := primorial q
  have P_pos : 0 < P := primorial_pos q
  apply uniformConstruction_not_isUnimodal_of_dusart_count_direct
    primeCountingBounds consecutive qPrev_gt_two hk bound_pos primorial_large
    shellNumeric descentDefined
  · intro a ha
    let index := Nat.primeCounting' (a + 2 * P + 1) - 1
    have predecessor_gt : P < primeAt index :=
      primeAt_primeCounting_sub_one_gt_of_two_mul_lt P_pos (by omega)
    have indexDefined : k - 1 ≤ index := by
      have countMono := Nat.monotone_primeCounting'
        (show 2 * P + 1 ≤ a + 2 * P + 1 by omega)
      dsimp only [index]
      have definedP : k - 1 ≤ Nat.primeCounting' (2 * P + 1) - 1 := by
        simpa only [P] using descentDefined
      omega
    have leadingEq :
        realLeadingWeightSum (primesBelow (primeAt index)) (k - 2) =
          primeWeightSumBelow (primeAt (k - 2)) :=
      realLeadingWeightSum_primesBelow_primeAt _ _ (by omega)
    have fullLower :
        primeWeightSumBelow (P + 1) ≤
          realWeightSum (primesBelow (primeAt index)) := by
      change primeWeightSumBelow (P + 1) ≤ primeWeightSumBelow (primeAt index)
      exact primeWeightSumBelow_mono (by omega)
    have shellPositive :
        0 < primeWeightSumBelow (P + 1) -
          primeWeightSumBelow (primeAt (k - 2)) := by
      have factorPositive : (0 : Real) < ((2 * qPrev + 1 : Nat) : Real) := by
        positivity
      have productPositive := (show (0 : Real) < ((k - 1 : Nat) : Real) by
        exact_mod_cast (show 0 < k - 1 by omega)).trans descentWeight
      exact (mul_pos_iff.mp productPositive).resolve_right
        (fun h ↦ (not_lt_of_ge (le_of_lt factorPositive)) h.1) |>.2
    have complementPositive :
        0 < realWeightSum (primesBelow (primeAt index)) -
          realLeadingWeightSum (primesBelow (primeAt index)) (k - 2) := by
      rw [leadingEq]
      linarith
    have ratioLe := real_densityRatio_le_degree_div_weightSum_sub_leading
      (primesBelow (primeAt index)) (primesBelow_gt_one _)
      (primesBelow_weights_descending _) (k - 1) (by omega)
      (by simpa [primesBelow_primeAt_length] using indexDefined)
      (by
        have positive := complementPositive
        rw [← ratCast_weightSum, ← ratCast_leadingWeightSum] at positive
        have ratPositive :
            0 < weightSum (primesBelow (primeAt index)) -
              leadingWeightSum (primesBelow (primeAt index)) (k - 2) := by
          exact_mod_cast positive
        simpa only [show k - 1 - 1 = k - 2 by omega] using ratPositive)
    have castRatioLt :
        (densityRatio (primesBelow (primeAt index)) (k - 1) : Real) <
          ((2 * qPrev + 1 : Nat) : Real) := by
      rw [show k - 1 - 1 = k - 2 by omega] at ratioLe
      refine ratioLe.trans_lt ((div_lt_iff₀ complementPositive).2 ?_)
      rw [leadingEq]
      have thresholdNonneg : (0 : Real) ≤ ((2 * qPrev + 1 : Nat) : Real) := by
        positivity
      nlinarith [mul_le_mul_of_nonneg_left fullLower thresholdNonneg,
        descentWeight]
    exact_mod_cast castRatioLt
  · intro i hi
    let index := Nat.primeCounting (4 * P) + i
    have indexDefined : k - 1 ≤ index := by
      have countMono :
          Nat.primeCounting' (2 * P + 1) ≤ Nat.primeCounting (4 * P) := by
        dsimp only [Nat.primeCounting]
        exact Nat.monotone_primeCounting' (by omega)
      dsimp only [index]
      have definedP : k - 1 ≤ Nat.primeCounting' (2 * P + 1) - 1 := by
        simpa only [P] using descentDefined
      omega
    have primeUpper : primeAt index ≤ 9 * P := by
      apply primeAt_primeCounting_add_le_upper
      have hiP :
          i < Nat.primeCounting (9 * P) - Nat.primeCounting (4 * P) - 1 := by
        simpa only [P] using hi
      omega
    have fullUpper :
        realWeightSum (primesBelow (primeAt index)) ≤
          primeWeightSumBelow (9 * P + 1) := by
      change primeWeightSumBelow (primeAt index) ≤ primeWeightSumBelow (9 * P + 1)
      exact primeWeightSumBelow_mono (by omega)
    have entriesNonempty : primesBelow (primeAt index) ≠ [] := by
      intro empty
      have lengthZero : (primesBelow (primeAt index)).length = 0 := by simp [empty]
      rw [primesBelow_primeAt_length] at lengthZero
      omega
    have sumPositiveRat : 0 < weightSum (primesBelow (primeAt index)) :=
      weightSum_pos_of_ne_nil _ (primesBelow_gt_one _) entriesNonempty
    have sumPositive : 0 < realWeightSum (primesBelow (primeAt index)) := by
      rw [← ratCast_weightSum]
      exact_mod_cast sumPositiveRat
    have ratioLower := real_degree_div_weightSum_le_densityRatio
      (primesBelow (primeAt index)) (primesBelow_gt_one _) (k - 1)
      (by simpa [primesBelow_primeAt_length] using indexDefined) sumPositiveRat
    have boundNonneg : (0 : Real) ≤ (bound : Real) := by positivity
    have productUpper :
        (bound : Real) * realWeightSum (primesBelow (primeAt index)) <
          ((k - 1 : Nat) : Real) :=
      (mul_le_mul_of_nonneg_left fullUpper boundNonneg).trans_lt
        (by simpa only [P] using ascentWeight)
    have castRatioGt :
        (bound : Real) <
          (densityRatio (primesBelow (primeAt index)) (k - 1) : Real) :=
      ((lt_div_iff₀ sumPositive).2 productUpper).trans_le ratioLower
    exact_mod_cast castRatioGt

end

end PrimeFactorUnimodality
