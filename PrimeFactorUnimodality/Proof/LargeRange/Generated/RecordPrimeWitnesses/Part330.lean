import Mathlib.Tactic.NormNum.Prime
import PrimeFactorUnimodality.Helpers.PrimeSequence.Basic

import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordPrimeWitnesses.Part329

set_option autoImplicit false
set_option maxRecDepth 1000000

/-! Generated prime witnesses for the record-range cutoff, part 330. -/

namespace PrimeFactorUnimodality

def recordPrimeWitnessBlock330 : Finset Nat :=
  [
    387911, 387913, 387917, 387953, 387967, 387971, 387973, 387977, 388009, 388051,
    388057, 388067, 388081, 388099, 388109, 388111, 388117, 388133, 388159, 388163,
    388169, 388177, 388181, 388183, 388187, 388211, 388231, 388237, 388253, 388259,
    388273, 388277, 388301, 388313, 388319, 388351, 388363, 388369, 388373, 388391,
    388403, 388459, 388471, 388477, 388481, 388483, 388489, 388499, 388519, 388529,
    388541, 388567, 388573, 388621, 388651, 388657, 388673, 388691, 388693, 388697,
    388699, 388711, 388727, 388757, 388777, 388781, 388789, 388793, 388813, 388823,
    388837, 388859, 388879, 388891, 388897, 388901, 388903, 388931, 388933, 388937,
    388961, 388963, 388991, 389003, 389023, 389027, 389029, 389041, 389047, 389057,
    389083, 389089, 389099, 389111, 389117, 389141, 389149, 389161, 389167, 389171
  ].toFinset

set_option maxHeartbeats 0 in
-- Exact cardinality reduction for this generated finite prime block.
theorem recordPrimeWitnessBlock330_card :
    recordPrimeWitnessBlock330.card = 100 := by
  decide

set_option maxHeartbeats 0 in
-- Kernel primality checks for every generated witness in this block.
theorem recordPrimeWitnessBlock330_subset :
    recordPrimeWitnessBlock330 ⊆ Nat.primesBelow 500001 := by
  intro p hp
  simp only [recordPrimeWitnessBlock330, List.mem_toFinset,
    List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num [Nat.mem_primesBelow]

theorem recordPrimeWitnessBlock330_lower {p : Nat}
    (hp : p ∈ recordPrimeWitnessBlock330) : 387911 ≤ p := by
  simp only [recordPrimeWitnessBlock330, List.mem_toFinset,
    List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num

theorem recordPrimeWitnessBlock330_upper {p : Nat}
    (hp : p ∈ recordPrimeWitnessBlock330) : p ≤ 389171 := by
  simp only [recordPrimeWitnessBlock330, List.mem_toFinset,
    List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num

end PrimeFactorUnimodality
