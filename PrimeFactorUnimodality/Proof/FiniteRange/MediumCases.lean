import Mathlib.Tactic.NormNum
import PrimeFactorUnimodality.Helpers.SymmetricBounds.Main
import PrimeFactorUnimodality.Helpers.Unimodality.Certificate
import PrimeFactorUnimodality.Proof.FiniteRange.Generated.MediumWeightBounds
import PrimeFactorUnimodality.Proof.FiniteRange.MediumPrefixes
import PrimeFactorUnimodality.Proof.FiniteRange.MediumPrimeGaps

set_option autoImplicit false
set_option maxRecDepth 100000

/-! # Non-unimodality certificates for `21 ≤ k ≤ 48` -/

namespace PrimeFactorUnimodality

private theorem densityRatio15683_lt_45 (r : Nat) (hrLower : 20 ≤ r)
    (hrUpper : r ≤ 30) :
    densityRatio (primesBelow 15683) r < 45 := by
  have hentries := primesBelow_gt_one 15683
  have hlength : r ≤ (primesBelow 15683).length := by
    rw [primesBelow, Finset.length_sort]
    change r ≤ (Nat.primesBelow 15683).card
    rw [Nat.primesBelow_card_eq_primeCounting']
    apply hrUpper.trans
    rw [← show Nat.primeCounting' 127 = 30 by decide]
    exact Nat.monotone_primeCounting' (by norm_num)
  have hleading :
      leadingWeightSum (primesBelow 15683) (r - 1) ≤
        weightSum (primesBelow 113) := by
    calc
      leadingWeightSum (primesBelow 15683) (r - 1) ≤
          leadingWeightSum (primesBelow 15683) 29 :=
        leadingWeightSum_mono (primesBelow 15683) hentries (by omega)
      _ = weightSum (primesBelow 113) := leadingWeightSum15683_29
  have htotal := weightSumPrimesBelow15683Lower
  have hsmallUpper := weightSumPrimesBelow113Upper
  have hleadingUpper := hleading.trans hsmallUpper
  have hcomplement :
      0 < weightSum (primesBelow 15683) -
        leadingWeightSum (primesBelow 15683) (r - 1) := by
    norm_num at htotal hleadingUpper ⊢
    linarith
  calc
    densityRatio (primesBelow 15683) r ≤
        (r : Rat) /
          (weightSum (primesBelow 15683) -
            leadingWeightSum (primesBelow 15683) (r - 1)) :=
      densityRatio_le_degree_div_weightSum_sub_leading
        (primesBelow 15683) hentries (primesBelow_weights_descending 15683)
        r (by omega) hlength hcomplement
    _ < 45 := by
      rw [div_lt_iff₀ hcomplement]
      norm_num at htotal hleadingUpper ⊢
      have hrUpperRat : (r : Rat) ≤ 30 := by exact_mod_cast hrUpper
      linarith

private theorem five_lt_densityRatio15727 (r : Nat) (hrLower : 20 ≤ r)
    (hrUpper : r ≤ 30) :
    5 < densityRatio (primesBelow 15727) r := by
  have hentries := primesBelow_gt_one 15727
  have hlength : r ≤ (primesBelow 15727).length := by
    rw [primesBelow, Finset.length_sort]
    change r ≤ (Nat.primesBelow 15727).card
    rw [Nat.primesBelow_card_eq_primeCounting']
    apply hrUpper.trans
    rw [← show Nat.primeCounting' 127 = 30 by decide]
    exact Nat.monotone_primeCounting' (by norm_num)
  have htotalUpper := weightSumPrimesBelow15727Upper
  have htotalLower := weightSumPrimesBelow15727Lower
  have htotalPos : 0 < weightSum (primesBelow 15727) := by
    norm_num at htotalLower ⊢
    linarith
  apply lt_of_lt_of_le _
    (degree_div_weightSum_le_densityRatio (primesBelow 15727) hentries r
      hlength htotalPos)
  rw [lt_div_iff₀ htotalPos]
  norm_num at htotalUpper ⊢
  have hrLowerRat : (20 : Rat) ≤ r := by exact_mod_cast hrLower
  linarith

private theorem densityRatio31397_lt_73 (r : Nat) (hrLower : 31 ≤ r)
    (hrUpper : r ≤ 47) :
    densityRatio (primesBelow 31397) r < 73 := by
  have hentries := primesBelow_gt_one 31397
  have hlength : r ≤ (primesBelow 31397).length := by
    rw [primesBelow, Finset.length_sort]
    change r ≤ (Nat.primesBelow 31397).card
    rw [Nat.primesBelow_card_eq_primeCounting']
    apply hrUpper.trans
    rw [← show Nat.primeCounting' 223 = 47 by decide]
    exact Nat.monotone_primeCounting' (by norm_num)
  have hleading :
      leadingWeightSum (primesBelow 31397) (r - 1) ≤
        weightSum (primesBelow 211) := by
    calc
      leadingWeightSum (primesBelow 31397) (r - 1) ≤
          leadingWeightSum (primesBelow 31397) 46 :=
        leadingWeightSum_mono (primesBelow 31397) hentries (by omega)
      _ = weightSum (primesBelow 211) := leadingWeightSum31397_46
  have htotal := weightSumPrimesBelow31397Lower
  have hsmallUpper := weightSumPrimesBelow211Upper
  have hleadingUpper := hleading.trans hsmallUpper
  have hcomplement :
      0 < weightSum (primesBelow 31397) -
        leadingWeightSum (primesBelow 31397) (r - 1) := by
    norm_num at htotal hleadingUpper ⊢
    linarith
  calc
    densityRatio (primesBelow 31397) r ≤
        (r : Rat) /
          (weightSum (primesBelow 31397) -
            leadingWeightSum (primesBelow 31397) (r - 1)) :=
      densityRatio_le_degree_div_weightSum_sub_leading
        (primesBelow 31397) hentries (primesBelow_weights_descending 31397)
        r (by omega) hlength hcomplement
    _ < 73 := by
      rw [div_lt_iff₀ hcomplement]
      norm_num at htotal hleadingUpper ⊢
      have hrUpperRat : (r : Rat) ≤ 47 := by exact_mod_cast hrUpper
      linarith

private theorem nine_lt_densityRatio31469 (r : Nat) (hrLower : 31 ≤ r)
    (hrUpper : r ≤ 47) :
    9 < densityRatio (primesBelow 31469) r := by
  have hentries := primesBelow_gt_one 31469
  have hlength : r ≤ (primesBelow 31469).length := by
    rw [primesBelow, Finset.length_sort]
    change r ≤ (Nat.primesBelow 31469).card
    rw [Nat.primesBelow_card_eq_primeCounting']
    apply hrUpper.trans
    rw [← show Nat.primeCounting' 223 = 47 by decide]
    exact Nat.monotone_primeCounting' (by norm_num)
  have htotalUpper := weightSumPrimesBelow31469Upper
  have htotalLower := weightSumPrimesBelow31469Lower
  have htotalPos : 0 < weightSum (primesBelow 31469) := by
    norm_num at htotalLower ⊢
    linarith
  apply lt_of_lt_of_le _
    (degree_div_weightSum_le_densityRatio (primesBelow 31469) hentries r
      hlength htotalPos)
  rw [lt_div_iff₀ htotalPos]
  norm_num at htotalUpper ⊢
  have hrLowerRat : (31 : Rat) ≤ r := by exact_mod_cast hrLower
  linarith

/-- Every density in the Wang--Crapis medium range has a certified strict
descent followed by a strict ascent. -/
theorem mediumRangePrimeFactorDensity_not_isUnimodal
    (k : Nat) (hkLower : 21 ≤ k) (hkUpper : k ≤ 48) :
    ¬ IsUnimodal (primeFactorDensity k) := by
  by_cases hk : k ≤ 31
  · let certificate : ExplicitRatioValleyCertificate (k - 2) :=
      { descentPrime := 15683
        descentNext := 15727
        ascentPrime := 15727
        ascentNext := 15731
        descentConsecutive := consecutive15683_15727
        ascentConsecutive := consecutive15727_15731
        descentBeforeAscent := by norm_num
        ratioDefinedAtDescent := by
          apply le_trans (show k - 2 + 1 ≤ 30 by omega)
          rw [← show Nat.primeCounting' 127 = 30 by decide]
          exact Nat.monotone_primeCounting' (by norm_num)
        ratioDefinedAtAscent := by
          apply le_trans (show k - 2 + 1 ≤ 30 by omega)
          rw [← show Nat.primeCounting' 127 = 30 by decide]
          exact Nat.monotone_primeCounting' (by norm_num)
        descentRatio := by
          simpa [show k - 2 + 1 = k - 1 by omega] using
            densityRatio15683_lt_45 (k - 1) (by omega) (by omega)
        ascentRatio := by
          simpa [show k - 2 + 1 = k - 1 by omega] using
            five_lt_densityRatio15727 (k - 1) (by omega) (by omega) }
    simpa [show k - 2 + 2 = k by omega] using certificate.not_isUnimodal
  · have hkLower' : 32 ≤ k := by omega
    let certificate : ExplicitRatioValleyCertificate (k - 2) :=
      { descentPrime := 31397
        descentNext := 31469
        ascentPrime := 31469
        ascentNext := 31477
        descentConsecutive := consecutive31397_31469
        ascentConsecutive := consecutive31469_31477
        descentBeforeAscent := by norm_num
        ratioDefinedAtDescent := by
          apply le_trans (show k - 2 + 1 ≤ 47 by omega)
          rw [← show Nat.primeCounting' 223 = 47 by decide]
          exact Nat.monotone_primeCounting' (by norm_num)
        ratioDefinedAtAscent := by
          apply le_trans (show k - 2 + 1 ≤ 47 by omega)
          rw [← show Nat.primeCounting' 223 = 47 by decide]
          exact Nat.monotone_primeCounting' (by norm_num)
        descentRatio := by
          simpa [show k - 2 + 1 = k - 1 by omega] using
            densityRatio31397_lt_73 (k - 1) (by omega) (by omega)
        ascentRatio := by
          simpa [show k - 2 + 1 = k - 1 by omega] using
            nine_lt_densityRatio31469 (k - 1) (by omega) (by omega) }
    simpa [show k - 2 + 2 = k by omega] using certificate.not_isUnimodal

end PrimeFactorUnimodality
