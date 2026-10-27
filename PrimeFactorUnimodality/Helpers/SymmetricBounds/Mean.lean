import PrimeFactorUnimodality.Helpers.SymmetricBounds.Ratio
import PrimeFactorUnimodality.Mathlib.Combinatorics.Enumerative.PoissonBinomial

set_option autoImplicit false

/-! # Density-ratio bounds from a tilted Bernoulli mean

This interface uses the finite mean comparison rather than subtracting the
largest weights from the reciprocal-prime sum. The mean premise is an explicit
finite sum; analytic estimates must prove it before this lemma closes a descent.
-/

namespace PrimeFactorUnimodality

noncomputable section

/-- The tilted Bernoulli mean for the exact reciprocal weights in the density. -/
def tiltedPrimeWeightMean (entries : List Nat) (t : Real) : Real :=
  List.oddsMean ((entries.map (fun p => (primeWeight p : Real))).map (fun w => t * w))

private theorem cast_weightEsymm_eq_oddsCoeff (entries : List Nat) (r : Nat) :
    (weightEsymm entries r : Real) =
      List.oddsCoeff (entries.map (fun p => (primeWeight p : Real))) (r : Int) := by
  induction entries generalizing r with
  | nil =>
    cases r with
    | zero => simp [weightEsymm, List.oddsCoeff]
    | succ r =>
      have hzero : weightEsymm [] (r + 1) = 0 := by
        change (0 : Multiset Rat).esymm (r + 1) = 0
        exact Multiset.esymm_of_card_lt (by simp)
      rw [hzero]
      simp [List.oddsCoeff]
      omega
  | cons p entries ih =>
    cases r with
    | zero => simp [weightEsymm, List.oddsCoeff_zero]
    | succ r =>
      have hc : weightEsymm (p :: entries) (r + 1) =
          weightEsymm entries (r + 1) + primeWeight p * weightEsymm entries r := by
        change (Multiset.cons (primeWeight p) (entries.map primeWeight : Multiset Rat)).esymm
          (r + 1) = _
        exact esymm_cons_succ _ _ _
      have hk : ((r + 1 : Nat) : Int) - 1 = (r : Int) := by omega
      rw [hc, Rat.cast_add, Rat.cast_mul, ih (r + 1), ih r]
      simp only [List.map_cons, List.oddsCoeff, hk]

/-- A strict mean bound gives the strict density-ratio bound needed at a descent. -/
theorem densityRatio_lt_of_lt_tiltedPrimeWeightMean
    (entries : List Nat) (hentries : forall p, Membership.mem entries p -> 1 < p)
    (r : Nat) (hr : 1 <= r) (t : Real) (ht : 0 < t)
    (hmean : (r : Real) < tiltedPrimeWeightMean entries t) :
    (densityRatio entries r : Real) < t := by
  let s : List Real := entries.map (fun p => (primeWeight p : Real))
  have hs : forall a, Membership.mem s a -> 0 < a := by
    intro a ha
    simp only [s, List.mem_map] at ha
    cases ha with
    | intro p hp =>
      rw [<- hp.2]
      exact_mod_cast primeWeight_pos p (hentries p hp.1)
  have hst : forall a, Membership.mem (s.map (fun w => t * w)) a -> 0 < a := by
    intro a ha
    simp only [List.mem_map] at ha
    cases ha with
    | intro w hw =>
      rw [<- hw.2]
      exact mul_pos ht (hs w hw.1)
  have hm : (r : Real) < List.oddsMean (s.map (fun w => t * w)) := hmean
  have hlen := List.oddsMean_le_length (s.map (fun w => t * w)) hst
  have hrlen : r <= entries.length := by
    simp only [List.length_map, s] at hlen
    have hlt : (r : Real) < entries.length := hm.trans_le hlen
    exact (by exact_mod_cast hlt : r < entries.length).le
  have hc := List.esymm_prev_lt_mul_of_lt_oddsMean s hs t ht r hr hm
  rw [<- List.oddsCoeff_nat_eq_esymm, <- List.oddsCoeff_nat_eq_esymm] at hc
  change List.oddsCoeff (entries.map (fun p => (primeWeight p : Real))) _ <
    t * List.oddsCoeff (entries.map (fun p => (primeWeight p : Real))) _ at hc
  rw [<- cast_weightEsymm_eq_oddsCoeff, <- cast_weightEsymm_eq_oddsCoeff] at hc
  have hden : (0 : Real) < (weightEsymm entries r : Real) := by
    exact_mod_cast weightEsymm_pos entries hentries r hrlen
  rw [densityRatio_eq_weightEsymm_ratio entries hentries r]
  push_cast
  have heq : ((weightEsymm entries (r - 1) : Real) / (weightEsymm entries r : Real)) *
      (weightEsymm entries r : Real) = (weightEsymm entries (r - 1) : Real) := by
    field_simp
  by_contra hnot
  have hle := mul_le_mul_of_nonneg_right (le_of_not_gt hnot) hden.le
  nlinarith only [hc, heq, hle]

end

end PrimeFactorUnimodality
