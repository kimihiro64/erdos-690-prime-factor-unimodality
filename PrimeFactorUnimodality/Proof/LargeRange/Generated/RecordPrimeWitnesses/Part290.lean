import Mathlib.Tactic.NormNum.Prime
import PrimeFactorUnimodality.Helpers.PrimeSequence.Basic

import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordPrimeWitnesses.Part289

set_option autoImplicit false
set_option maxRecDepth 1000000

/-! Generated prime witnesses for the record-range cutoff, part 290. -/

namespace PrimeFactorUnimodality

def recordPrimeWitnessBlock290 : Finset Nat :=
  [
    336353, 336361, 336373, 336397, 336403, 336419, 336437, 336463, 336491, 336499,
    336503, 336521, 336527, 336529, 336533, 336551, 336563, 336571, 336577, 336587,
    336593, 336599, 336613, 336631, 336643, 336649, 336653, 336667, 336671, 336683,
    336689, 336703, 336727, 336757, 336761, 336767, 336769, 336773, 336793, 336799,
    336803, 336823, 336827, 336829, 336857, 336863, 336871, 336887, 336899, 336901,
    336911, 336929, 336961, 336977, 336983, 336989, 336997, 337013, 337021, 337031,
    337039, 337049, 337069, 337081, 337091, 337097, 337121, 337153, 337189, 337201,
    337213, 337217, 337219, 337223, 337261, 337277, 337279, 337283, 337291, 337301,
    337313, 337327, 337339, 337343, 337349, 337361, 337367, 337369, 337397, 337411,
    337427, 337453, 337457, 337487, 337489, 337511, 337517, 337529, 337537, 337541
  ].toFinset

set_option maxHeartbeats 0 in
-- Exact cardinality reduction for this generated finite prime block.
theorem recordPrimeWitnessBlock290_card :
    recordPrimeWitnessBlock290.card = 100 := by
  decide

set_option maxHeartbeats 0 in
-- Kernel primality checks for every generated witness in this block.
theorem recordPrimeWitnessBlock290_subset :
    recordPrimeWitnessBlock290 ⊆ Nat.primesBelow 500001 := by
  intro p hp
  simp only [recordPrimeWitnessBlock290, List.mem_toFinset,
    List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num [Nat.mem_primesBelow]

theorem recordPrimeWitnessBlock290_lower {p : Nat}
    (hp : p ∈ recordPrimeWitnessBlock290) : 336353 ≤ p := by
  simp only [recordPrimeWitnessBlock290, List.mem_toFinset,
    List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num

theorem recordPrimeWitnessBlock290_upper {p : Nat}
    (hp : p ∈ recordPrimeWitnessBlock290) : p ≤ 337541 := by
  simp only [recordPrimeWitnessBlock290, List.mem_toFinset,
    List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num

end PrimeFactorUnimodality
