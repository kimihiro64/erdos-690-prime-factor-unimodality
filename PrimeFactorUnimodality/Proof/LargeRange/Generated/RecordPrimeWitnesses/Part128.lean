import Mathlib.Tactic.NormNum.Prime
import PrimeFactorUnimodality.Helpers.PrimeSequence.Basic

import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordPrimeWitnesses.Part127

set_option autoImplicit false
set_option maxRecDepth 1000000

/-! Generated prime witnesses for the record-range cutoff, part 128. -/

namespace PrimeFactorUnimodality

def recordPrimeWitnessBlock128 : Finset Nat :=
  [
    136393, 136397, 136399, 136403, 136417, 136421, 136429, 136447, 136453, 136463,
    136471, 136481, 136483, 136501, 136511, 136519, 136523, 136531, 136537, 136541,
    136547, 136559, 136573, 136601, 136603, 136607, 136621, 136649, 136651, 136657,
    136691, 136693, 136709, 136711, 136727, 136733, 136739, 136751, 136753, 136769,
    136777, 136811, 136813, 136841, 136849, 136859, 136861, 136879, 136883, 136889,
    136897, 136943, 136949, 136951, 136963, 136973, 136979, 136987, 136991, 136993,
    136999, 137029, 137077, 137087, 137089, 137117, 137119, 137131, 137143, 137147,
    137153, 137177, 137183, 137191, 137197, 137201, 137209, 137219, 137239, 137251,
    137273, 137279, 137303, 137321, 137339, 137341, 137353, 137359, 137363, 137369,
    137383, 137387, 137393, 137399, 137413, 137437, 137443, 137447, 137453, 137477
  ].toFinset

set_option maxHeartbeats 0 in
-- Exact cardinality reduction for this generated finite prime block.
theorem recordPrimeWitnessBlock128_card :
    recordPrimeWitnessBlock128.card = 100 := by
  decide

set_option maxHeartbeats 0 in
-- Kernel primality checks for every generated witness in this block.
theorem recordPrimeWitnessBlock128_subset :
    recordPrimeWitnessBlock128 ⊆ Nat.primesBelow 500001 := by
  intro p hp
  simp only [recordPrimeWitnessBlock128, List.mem_toFinset,
    List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num [Nat.mem_primesBelow]

theorem recordPrimeWitnessBlock128_lower {p : Nat}
    (hp : p ∈ recordPrimeWitnessBlock128) : 136393 ≤ p := by
  simp only [recordPrimeWitnessBlock128, List.mem_toFinset,
    List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num

theorem recordPrimeWitnessBlock128_upper {p : Nat}
    (hp : p ∈ recordPrimeWitnessBlock128) : p ≤ 137477 := by
  simp only [recordPrimeWitnessBlock128, List.mem_toFinset,
    List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num

end PrimeFactorUnimodality
