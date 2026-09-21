import Mathlib.Tactic.NormNum.Prime
import PrimeFactorUnimodality.Helpers.PrimeSequence.Basic

import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordPrimeWitnesses.Part286

set_option autoImplicit false
set_option maxRecDepth 1000000

/-! Generated prime witnesses for the record-range cutoff, part 287. -/

namespace PrimeFactorUnimodality

def recordPrimeWitnessBlock287 : Finset Nat :=
  [
    332467, 332471, 332473, 332477, 332489, 332509, 332513, 332561, 332567, 332569,
    332573, 332611, 332617, 332623, 332641, 332687, 332699, 332711, 332729, 332743,
    332749, 332767, 332779, 332791, 332803, 332837, 332851, 332873, 332881, 332887,
    332903, 332921, 332933, 332947, 332951, 332987, 332989, 332993, 333019, 333023,
    333029, 333031, 333041, 333049, 333071, 333097, 333101, 333103, 333107, 333131,
    333139, 333161, 333187, 333197, 333209, 333227, 333233, 333253, 333269, 333271,
    333283, 333287, 333299, 333323, 333331, 333337, 333341, 333349, 333367, 333383,
    333397, 333419, 333427, 333433, 333439, 333449, 333451, 333457, 333479, 333491,
    333493, 333497, 333503, 333517, 333533, 333539, 333563, 333581, 333589, 333623,
    333631, 333647, 333667, 333673, 333679, 333691, 333701, 333713, 333719, 333721
  ].toFinset

set_option maxHeartbeats 0 in
-- Exact cardinality reduction for this generated finite prime block.
theorem recordPrimeWitnessBlock287_card :
    recordPrimeWitnessBlock287.card = 100 := by
  decide

set_option maxHeartbeats 0 in
-- Kernel primality checks for every generated witness in this block.
theorem recordPrimeWitnessBlock287_subset :
    recordPrimeWitnessBlock287 ⊆ Nat.primesBelow 500001 := by
  intro p hp
  simp only [recordPrimeWitnessBlock287, List.mem_toFinset,
    List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num [Nat.mem_primesBelow]

theorem recordPrimeWitnessBlock287_lower {p : Nat}
    (hp : p ∈ recordPrimeWitnessBlock287) : 332467 ≤ p := by
  simp only [recordPrimeWitnessBlock287, List.mem_toFinset,
    List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num

theorem recordPrimeWitnessBlock287_upper {p : Nat}
    (hp : p ∈ recordPrimeWitnessBlock287) : p ≤ 333721 := by
  simp only [recordPrimeWitnessBlock287, List.mem_toFinset,
    List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num

end PrimeFactorUnimodality
