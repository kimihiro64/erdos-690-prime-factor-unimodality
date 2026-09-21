import Mathlib.Tactic.NormNum.Prime
import PrimeFactorUnimodality.Helpers.PrimeSequence.Basic

import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordPrimeWitnesses.Part200

set_option autoImplicit false
set_option maxRecDepth 1000000

/-! Generated prime witnesses for the record-range cutoff, part 201. -/

namespace PrimeFactorUnimodality

def recordPrimeWitnessBlock201 : Finset Nat :=
  [
    224743, 224759, 224771, 224797, 224813, 224831, 224863, 224869, 224881, 224891,
    224897, 224909, 224911, 224921, 224929, 224947, 224951, 224969, 224977, 224993,
    225023, 225037, 225061, 225067, 225077, 225079, 225089, 225109, 225119, 225133,
    225143, 225149, 225157, 225161, 225163, 225167, 225217, 225221, 225223, 225227,
    225241, 225257, 225263, 225287, 225289, 225299, 225307, 225341, 225343, 225347,
    225349, 225353, 225371, 225373, 225383, 225427, 225431, 225457, 225461, 225479,
    225493, 225499, 225503, 225509, 225523, 225527, 225529, 225569, 225581, 225583,
    225601, 225611, 225613, 225619, 225629, 225637, 225671, 225683, 225689, 225697,
    225721, 225733, 225749, 225751, 225767, 225769, 225779, 225781, 225809, 225821,
    225829, 225839, 225859, 225871, 225889, 225919, 225931, 225941, 225943, 225949
  ].toFinset

set_option maxHeartbeats 0 in
-- Exact cardinality reduction for this generated finite prime block.
theorem recordPrimeWitnessBlock201_card :
    recordPrimeWitnessBlock201.card = 100 := by
  decide

set_option maxHeartbeats 0 in
-- Kernel primality checks for every generated witness in this block.
theorem recordPrimeWitnessBlock201_subset :
    recordPrimeWitnessBlock201 ⊆ Nat.primesBelow 500001 := by
  intro p hp
  simp only [recordPrimeWitnessBlock201, List.mem_toFinset,
    List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num [Nat.mem_primesBelow]

theorem recordPrimeWitnessBlock201_lower {p : Nat}
    (hp : p ∈ recordPrimeWitnessBlock201) : 224743 ≤ p := by
  simp only [recordPrimeWitnessBlock201, List.mem_toFinset,
    List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num

theorem recordPrimeWitnessBlock201_upper {p : Nat}
    (hp : p ∈ recordPrimeWitnessBlock201) : p ≤ 225949 := by
  simp only [recordPrimeWitnessBlock201, List.mem_toFinset,
    List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num

end PrimeFactorUnimodality
