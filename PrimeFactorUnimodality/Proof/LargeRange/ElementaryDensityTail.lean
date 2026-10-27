import PrimeFactorUnimodality.Helpers.Analytic.ClassificationPrimorialWindow
import PrimeFactorUnimodality.Helpers.Analytic.ElementaryLaterGap
import PrimeFactorUnimodality.Helpers.Analytic.ElementaryTailRatioBounds
import PrimeFactorUnimodality.Helpers.PrimeSequence.CRTCompositeBlock
import PrimeFactorUnimodality.Helpers.Unimodality.Certificate

set_option autoImplicit false

/-! # An unconditional density valley for every large k -/

namespace PrimeFactorUnimodality

noncomputable section

theorem elementary_tail_not_isUnimodal (k : Nat) (hk : 38001 <= k) :
    Not (IsUnimodal (primeFactorDensity k)) := by
  let r := k - 1
  have hrNat : 38000 <= r := by dsimp only [r]; omega
  have hr : (38000 : Real) <= r := by exact_mod_cast hrNat
  cases exists_classification_primorial_window r hr with
  | intro p hp =>
    cases hp with
    | intro q hq =>
      let P := primorial q
      have hpair := hq.1
      have hpLarge := hq.2.1
      have ht := hq.2.2.1
      have hL := hq.2.2.2.1
      have hP := hq.2.2.2.2.2.1
      have hM := hq.2.2.2.2.2.2
      have hcrt : Exists (fun a : Nat => And (a < P)
          (And (2 * p <= primeGap (Nat.primeCounting' (a + 2 * P + 1) - 1))
            (P < primeAt (Nat.primeCounting' (a + 2 * P + 1) - 1)))) := by
        simpa only [<- primorial_eq_prod_primesLE] using
          exists_large_primeGap_with_predecessor_of_consecutive hpair (by omega)
      cases hcrt with
      | intro a ha =>
        let d := Nat.primeCounting' (a + 2 * P + 1) - 1
        have hMean := elementary_tail_mean_lower r P (primeAt d) hr hP hL ha.2.2
        have hLength : r <= (primesBelow (primeAt d)).length := by
          have hle := tiltedPrimeWeightMean_le_length (primesBelow (primeAt d))
            (primesBelow_gt_one _) (classificationT r) (by linarith [classificationT_lower r hr])
          have hlt : (r : Real) < (primesBelow (primeAt d)).length := hMean.trans_le hle
          exact (by exact_mod_cast hlt : r < (primesBelow (primeAt d)).length).le
        have hDef : r <= d := by simpa only [primesBelow_primeAt_length] using hLength
        have hDesc := densityRatio_lt_of_lt_tiltedPrimeWeightMean
          (primesBelow (primeAt d)) (primesBelow_gt_one _) r (by omega)
            (classificationT r) (by linarith [classificationT_lower r hr]) hMean
        have hDescGap : classificationT r < (primeGap d : Real) + 1 := by
          have hg : 2 * (p : Real) <= (primeGap d : Real) := by exact_mod_cast ha.2.1
          linarith
        have hDescRat : densityRatio (primesBelow (primeAt d)) r < ((primeGap d + 1 : Nat) : Rat) := by
          exact_mod_cast hDesc.trans hDescGap
        cases exists_later_elementary_small_gap P hP with
        | intro j hj =>
          have hPr : 0 < P := primorial_pos q
          have hCut : 2 < a + 2 * P + 1 := by
            have hqPrime := hpair.right_prime.two_le
            have hqP : q <= P := le_primorial_self
            omega
          have hCountPos : 0 < Nat.primeCounting' (a + 2 * P + 1) := by
            rw [Nat.pos_iff_ne_zero, ne_eq, Nat.primeCounting'_eq_zero_iff]
            omega
          have hCountLe : Nat.primeCounting' (a + 2 * P + 1) <= Nat.primeCounting (4 * P) :=
            Nat.monotone_primeCounting' (by omega)
          have hdj : d < j := by dsimp only [d]; omega
          have hAscDef : r <= j := hDef.trans hdj.le
          have hAscLength : r <= (primesBelow (primeAt j)).length := by
            simpa only [primesBelow_primeAt_length] using hAscDef
          have hAscWeight := elementary_tail_ascent_weight_bound r P (primeAt j) (primeGap j)
            hr hP (one_lt_primeAt j).le hj.2.1 hM hj.2.2
          rw [<- ratCast_weightSum_primesBelow] at hAscWeight
          have hAscNum : ((primeGap j + 1 : Nat) : Rat) * weightSum (primesBelow (primeAt j)) <
              (r : Rat) := by
            exact_mod_cast hAscWeight
          have hNonempty : Not (primesBelow (primeAt j) = []) := by
            intro h
            simp only [h, List.length_nil] at hAscLength
            omega
          have hSum := weightSum_pos_of_ne_nil _ (primesBelow_gt_one _) hNonempty
          have hAscRat := bound_lt_densityRatio_of_bound_mul_weightSum_lt_degree
            (primesBelow (primeAt j)) (primesBelow_gt_one _) r hAscLength
              ((primeGap j + 1 : Nat) : Rat) hSum hAscNum
          let cert : RatioValleyCertificate (k - 2) :=
            { descentIndex := d
              ascentIndex := j
              ratioDefinedAtDescent := by
                change k - 2 + 1 <= d
                simpa only [show k - 2 + 1 = k - 1 by omega] using hDef
              ratioDefinedAtAscent := by
                change k - 2 + 1 <= j
                simpa only [show k - 2 + 1 = k - 1 by omega] using hAscDef
              descentBeforeAscent := hdj
              descentRatio := by
                simpa only [show k - 2 + 1 = k - 1 by omega] using hDescRat
              ascentRatio := by
                simpa only [show k - 2 + 1 = k - 1 by omega] using hAscRat }
          simpa only [show k - 2 + 2 = k by omega] using cert.not_isUnimodal

end

end PrimeFactorUnimodality
