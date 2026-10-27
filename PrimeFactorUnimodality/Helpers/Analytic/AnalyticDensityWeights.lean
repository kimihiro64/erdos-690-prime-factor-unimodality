import PrimeFactorUnimodality.Helpers.Analytic.PrimeWeightSum
import PrimeFactorUnimodality.Helpers.Analytic.ShiftedReciprocalUpper
import PrimeFactorUnimodality.Helpers.Analytic.SmoothedPrimeAbel
import PrimeFactorUnimodality.Helpers.SymmetricBounds.Mean

set_option autoImplicit false

/-! # Analytic prime sums and exact density weights -/

namespace PrimeFactorUnimodality

open Real Finset

theorem tiltedPrimeWeightMean_eq_sum (entries : List Nat)
    (he : forall p, Membership.mem entries p -> 1 < p) (t : Real) (ht : 0 < t) :
    tiltedPrimeWeightMean entries t =
      (entries.map (fun p => t / (((p - 1 : Nat) : Real) + t))).sum := by
  unfold tiltedPrimeWeightMean List.oddsMean
  simp only [List.map_map, Function.comp_def]
  apply congrArg List.sum
  apply List.map_congr_left
  intro p hp
  have hp0 : (0 : Real) < ((p - 1 : Nat) : Real) := by
    exact_mod_cast Nat.sub_pos_of_lt (he p hp)
  simp only [primeWeight, Rat.cast_div, Rat.cast_one, Rat.cast_natCast]
  have hden : Not (1 + t * (1 / ((p - 1 : Nat) : Real)) = 0) := by positivity
  have hplus : Not (((p - 1 : Nat) : Real) + t = 0) := by positivity
  field_simp
  <;> ring

theorem tiltedPrimeWeightMean_primesBelow (b : Nat) (t : Real) (ht : 0 < t) :
    tiltedPrimeWeightMean (primesBelow b) t =
      (Nat.primesBelow b).sum (fun p => t / (((p - 1 : Nat) : Real) + t)) := by
  rw [tiltedPrimeWeightMean_eq_sum _ (primesBelow_gt_one b) t ht]
  change
    (Multiset.map (fun p => t / (((p - 1 : Nat) : Real) + t))
      (((Nat.primesBelow b).sort (fun a b => a <= b)) : Multiset Nat)).sum = _
  rw [Finset.sort_eq]
  rfl

theorem smoothedPrimeSum_mul_le_tiltedMean (t X : Real) (b : Nat)
    (ht : 0 < t) (hX : 0 <= X) (hXb : X < b) :
    t * Mertens.smoothedPrimeSum t X <= tiltedPrimeWeightMean (primesBelow b) t := by
  rw [tiltedPrimeWeightMean_primesBelow b t ht]
  let s := (Finset.Icc 0 (Nat.floor X)).filter Nat.Prime
  have hsubset : s <= Nat.primesBelow b := by
    intro p hp
    have hm := Finset.mem_filter.mp hp
    have hpFloor : (p : Real) <= (Nat.floor X : Nat) := by
      exact_mod_cast (Finset.mem_Icc.mp hm.1).2
    have hpX : (p : Real) <= X := hpFloor.trans (Nat.floor_le hX)
    exact Nat.mem_primesBelow.mpr (And.intro (by exact_mod_cast hpX.trans_lt hXb) hm.2)
  have hsum : t * Mertens.smoothedPrimeSum t X =
      s.sum (fun p => t / ((p : Real) + t)) := by
    simp only [Mertens.smoothedPrimeSum, s, Finset.sum_filter, Finset.mul_sum,
      mul_ite, mul_zero, mul_one_div]
  rw [hsum]
  have hcmp : s.sum (fun p => t / ((p : Real) + t)) <=
      s.sum (fun p => t / (((p - 1 : Nat) : Real) + t)) := by
    apply Finset.sum_le_sum
    intro p hp
    have hpred : (0 : Real) <= ((p - 1 : Nat) : Real) := Nat.cast_nonneg _
    apply div_le_div_of_nonneg_left ht.le (by linarith)
    have hpredle : (((p - 1 : Nat) : Real)) <= (p : Real) := by
      exact_mod_cast Nat.sub_le p 1
    linarith only [hpredle]
  apply hcmp.trans
  apply Finset.sum_le_sum_of_subset_of_nonneg hsubset
  intro p hp hnot
  positivity

theorem tiltedPrimeWeightMean_le_length (entries : List Nat)
    (he : forall p, Membership.mem entries p -> 1 < p) (t : Real) (ht : 0 < t) :
    tiltedPrimeWeightMean entries t <= entries.length := by
  rw [tiltedPrimeWeightMean_eq_sum entries he t ht]
  have hsum : (entries.map (fun p => t / (((p - 1 : Nat) : Real) + t))).sum <=
      (entries.map (fun _ => (1 : Real))).sum := by
    apply List.sum_le_sum
    intro i hi
    have hp : 0 < ((i - 1 : Nat) : Real) := by
      exact_mod_cast Nat.sub_pos_of_lt (he i hi)
    exact (div_le_one (by linarith)).mpr (by linarith)
  simpa using hsum

theorem primeWeightSumBelow_eq_shifted (b : Nat) (hb : 1 <= b) :
    primeWeightSumBelow b = Mertens.primeShiftedReciprocalSum (b - 1 : Nat) := by
  rw [primeWeightSumBelow_eq_finset]
  unfold Mertens.primeShiftedReciprocalSum
  rw [Nat.floor_natCast, <- Finset.sum_filter]
  have hs : Nat.primesBelow b = (Finset.Icc 0 (b - 1)).filter Nat.Prime := by
    ext p
    simp only [Nat.mem_primesBelow, Finset.mem_filter, Finset.mem_Icc]
    constructor
    next =>
      intro hp
      exact And.intro (And.intro (Nat.zero_le p) (by omega)) hp.2
    next =>
      intro hp
      exact And.intro (by omega) hp.2
  rw [hs]
  apply Finset.sum_congr rfl
  intro p hp
  have hp1 := (Finset.mem_filter.mp hp).2.one_lt
  rw [Nat.cast_sub (by omega : 1 <= p), Nat.cast_one]

end PrimeFactorUnimodality
